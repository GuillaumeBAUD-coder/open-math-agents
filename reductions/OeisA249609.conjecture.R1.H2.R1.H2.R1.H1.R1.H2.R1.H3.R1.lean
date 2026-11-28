import OMAReductions.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H2_R1

/-! Periodic binomial-column certificates for OEIS A249609.
The periodicity theorem is due to PanPapag. The binary parity fold and the
falling-factorial representation follow the reductions in this chain. -/

namespace A249609ColumnCertificates

open OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1

private theorem weight_half (n : ℕ) :
    (Nat.digits 2 n).count 1 = (Nat.digits 2 (n/2)).count 1 + n%2 := by
  have hh := count_ones_append (n/2) 1 (n%2) (by simpa using Nat.mod_lt n (by decide : 0 < 2))
  rw [pow_one, Nat.div_add_mod'] at hh
  change (Nat.digits 2 n).count 1 = (Nat.digits 2 (n / 2)).count 1 + (Nat.digits 2 (n % 2)).count 1 at hh
  rw [hh]
  have h : n%2 = 0 ∨ n%2 = 1 := by omega
  rcases h with h | h <;> rw [h] <;> rfl

private theorem xor_weight (a b : ℕ) : (Nat.digits 2 (a ^^^ b)).count 1 % 2 = ((Nat.digits 2 a).count 1 + (Nat.digits 2 b).count 1) % 2 := by
  induction h : a+b using Nat.strong_induction_on generalizing a b with
  | h n ih =>
    by_cases hzero : n = 0
    · have ha : a = 0 := by omega
      have hb : b = 0 := by omega
      subst a; subst b; rfl
    have half := ih (a/2+b/2) (by omega) (a/2) (b/2) rfl
    have ha := weight_half a
    have hb := weight_half b
    have hab := weight_half (a ^^^ b)
    rw [Nat.xor_div_two] at hab
    have hmod := Nat.xor_mod_two_eq (m := a) (n := b)
    omega

/-- Folding the two halves with xor preserves the parity and halves the bit width. -/
private theorem fold_certificate (i n : ℕ) (h :
    (Nat.rec (motive := fun _ => ℕ → ℕ) (fun v => (Nat.digits 2 v).count 1 % 2)
      (fun j f v => let base := 2^(8 * 2^j); f ((v / base) ^^^ (v % base))) i n) = 0) :
    (Nat.digits 2 n).count 1 % 2 = 0 := by
  let count := Nat.rec (motive := fun _ => ℕ → ℕ) (fun v => (Nat.digits 2 v).count 1 % 2)
      (fun j f v => let base := 2^(8 * 2^j); f ((v / base) ^^^ (v % base)))
  have spec (j v : ℕ) : count j v = (Nat.digits 2 v).count 1 % 2 := by
    induction j generalizing v with
    | zero => rfl
    | succ j ih =>
      let w := 8*2^j
      change count j ((v / 2^w) ^^^ (v % 2^w)) = _
      rw [ih,xor_weight]
      have hh := count_ones_append (v / 2^w) w (v%2^w) (Nat.mod_lt _ (by positivity))
      rw [Nat.div_add_mod'] at hh
      exact congrArg (· % 2) hh.symm
  exact (spec i n).symm.trans h


private lemma extend_pow_mod {n r d m s : ℕ} (b : ℕ) (h : 2^n ≡ r [MOD d])
    (hm : n+n+b = m) (hs : (r*r*2^b)%d = s) : 2^m ≡ s [MOD d] := by
  subst m s
  rw [pow_add, pow_add]
  exact ((h.mul h).mul (Nat.ModEq.refl _)).trans (Nat.mod_modEq _ _).symm


set_option maxHeartbeats 3000000 in
private theorem verify_word_table (ds : List (Bool × ℕ)) (w t d : ℕ) (hd : 0 < d)
    (hc : ∀ s ∈ ds, s.2 < 2^t) (trace : List ℕ) :
    let cap := 4194304
    let fill (b : Bool) (j : ℕ) : ℕ := if b then 2^j-1 else 0
    let fold := Nat.rec (motive := fun _ => ℕ → ℕ) (fun v => (Nat.digits 2 v).count 1 % 2)
      (fun j f v => let base := 2^(8 * 2^j); f ((v / base) ^^^ (v % base)))
    let step (st : ℕ) (s : ℕ × ℕ) :=
      let v := ((st/2) <<< s.1) + s.2
      2*(v % d) + ((st % 2 + fold 19 (v / d)) % 2)
    let bits (s : Bool × ℕ) : List (ℕ × ℕ) :=
      List.replicate (w/cap) (cap, fill s.1 cap) ++ [(w%cap, fill s.1 (w%cap)),(t,s.2)]
    let chunks := ds.reverse.flatMap bits
    chunks.length = trace.length →
      ((chunks.zip trace).foldr (fun r f i => (step i r.1 == r.2) && f r.2)
        (fun i => i%2 == 0) 0) = true →
      (Nat.digits 2 (ds.foldr (fun s v => (((v <<< w) + fill s.1 w) <<< t) + s.2) 0 / d)).count 1 % 2 = 0 := by
  intro cap fill fold step bits chunks hlen cert
  let ones (x : ℕ) := (Nat.digits 2 x).count 1
  let good (st n : ℕ) : Prop := st/2 = n % d ∧ st%2 = ones (n / d) % 2
  have fold_ok (j v : ℕ) : fold j v = ones v % 2 := by
    induction j generalizing v with
    | zero => rfl
    | succ j ih =>
      let width := 8*2^j
      change fold j ((v / 2^width) ^^^ (v % 2^width)) = _
      rw [ih,show ones ((v / 2^width) ^^^ (v % 2^width))%2 = (ones (v/2^width) + ones (v%2^width))%2 from xor_weight _ _]
      have h := count_ones_append (v/2^width) width (v%2^width) (Nat.mod_lt _ (by positivity))
      rw [Nat.div_add_mod'] at h
      exact congrArg (· % 2) h.symm
  have step_ok (st : ℕ) (n j c : ℕ) (hs : good st n) (hlt : c < 2^j) :
      good (step st (j,c)) ((n <<< j) + c) := by
    obtain ⟨hrem,hpar⟩ := hs
    have he : n*2^j+c = (n%d * 2^j+c) + (n/d * 2^j)*d := by
      calc
        n*2^j+c = (n%d+d*(n/d))*2^j+c := by rw [Nat.mod_add_div]
        _ = _ := by ring
    have hv : (n%d * 2^j+c)/d < 2^j := by
      apply (Nat.div_lt_iff_lt_mul hd).mpr
      have h := Nat.mul_le_mul_right (2^j) (Nat.succ_le_of_lt (Nat.mod_lt n hd))
      rw [Nat.succ_mul] at h
      nlinarith only [h,hlt]
    change (2*((((st/2) <<< j) + c)%d) + ((st%2 + fold 19 ((((st/2) <<< j) + c)/d))%2))/2 = _ ∧
      (2*((((st/2) <<< j) + c)%d) + ((st%2 + fold 19 ((((st/2) <<< j) + c)/d))%2))%2 = _
    simp only [Nat.shiftLeft_eq,hrem,he,Nat.add_mul_mod_self_right, Nat.add_mul_div_right _ _ hd]
    rw [Nat.add_comm ((n%d*2^j+c)/d), show ones ((n/d)*2^j+(n%d*2^j+c)/d) =
      ones (n/d) + ones ((n%d*2^j+c)/d) from count_ones_append _ _ _ hv]
    rw [fold_ok]
    omega
  have fill_lt (b : Bool) (i : ℕ) : fill b i < 2^i := by
    have h := Nat.two_pow_pos i
    cases b <;> simp [fill]
  have join (n i j : ℕ) (b : Bool) :
      (((n <<< i) + fill b i) <<< j) + fill b j = (n <<< (i+j)) + fill b (i+j) := by
    simp only [Nat.shiftLeft_eq, pow_add]
    cases b
    · simp [fill, mul_assoc]
    · simp only [fill,if_true,pow_add]
      have hi := Nat.two_pow_pos i
      have hj := Nat.two_pow_pos j
      rw [Nat.add_mul]
      have e := congrArg (fun z : ℕ => z * 2^j) (Nat.sub_add_cancel (show 1 ≤ 2^i by omega))
      simp only [Nat.add_mul, Nat.one_mul] at e
      rw [Nat.mul_assoc]
      omega
  have reps (st n : ℕ) (b : Bool) (m : ℕ) (hs : good st n) :
      good ((List.replicate m (cap,fill b cap)).foldl step st)
        ((n <<< (cap*m)) + fill b (cap*m)) := by
    induction m with
    | zero => simpa [fill] using hs
    | succ m ih =>
      rw [List.replicate_succ',List.foldl_append,List.foldl_cons,List.foldl_nil]
      have h := step_ok _ _ cap _ ih (fill_lt b cap)
      rw [join, ← Nat.mul_succ] at h
      exact h
  have ds_ok (xs : List (Bool × ℕ)) (hh : ∀ s ∈ xs, s.2 < 2^t) :
      good ((xs.reverse.flatMap bits).foldl step 0)
        (xs.foldr (fun s v => (((v <<< w) + fill s.1 w) <<< t) + s.2) 0) := by
    induction xs with
    | nil => simp [good,ones]
    | cons s xs ih =>
      have h := step_ok _ _ _ _ (reps _ _ s.1 (w/cap) (ih (fun x hx => hh x (by simp [hx])))) (fill_lt s.1 (w%cap))
      rw [join, Nat.add_comm (cap*(w/cap)), Nat.mod_add_div] at h
      simpa only [List.reverse_cons,List.flatMap_append,List.flatMap_singleton,bits,List.foldl_append,
        List.foldl_cons,List.foldl_nil,List.foldr_cons] using step_ok _ _ _ _ h (hh s (by simp))
  have valid (xs : List (ℕ × ℕ)) (ys : List ℕ) (i : ℕ) (he : xs.length = ys.length)
      (hv : ((xs.zip ys).foldr (fun r f i => (step i r.1 == r.2) && f r.2)
        (fun i => i%2 == 0) i) = true) : xs.foldl step i % 2 = 0 := by
    induction xs generalizing ys i with
    | nil => simpa using hv
    | cons x xs ih =>
      cases ys with
      | nil => simp at he
      | cons y ys =>
        simp only [List.zip_cons_cons,List.foldr_cons,Bool.and_eq_true,beq_iff_eq] at hv
        rw [List.foldl_cons,hv.1]
        exact ih ys y (Nat.succ.inj he) hv.2
  exact (ds_ok ds hc).2.symm.trans (valid chunks trace 0 hlen cert)


set_option maxHeartbeats 8000000 in
private theorem falling18 (x B : ℕ) (hx : 0 < x) (hB : B = 2251799813685248) :
    ([(false, 0), (true, 1896112385589248), (false, 1223405590579199), (true, 430197369060608), (false, 1583313975727487), (true, 1342499907841136), (false, 369012649234383), (true, 2141571347501048), (false, 24871845297935), (true, 2247491708383319), (false, 577924894832), (true, 2251739610991268), (false, 4853222763), (true, 2251799514034442), (false, 13896581), (true, 2251799813217068), (false, 10811), (true, 2251799813685095), (false, 0)] : List (Bool × ℕ)).foldr
      (fun s v => (v * x + (if s.1 then x-1 else 0)) * B + s.2) 0 =
      (x * B).descFactorial 18 := by
  let low (v c : ℕ) := (v * x + 0) * B + c
  let high (v c : ℕ) := (v * x + (x-1)) * B + c
  calc
    _ = (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low 0 0) 2251799813685095) 10811) 2251799813217068) 13896581) 2251799514034442) 4853222763) 2251739610991268) 577924894832) 2247491708383319) 24871845297935) 2141571347501048) 369012649234383) 1342499907841136) 1583313975727487) 430197369060608) 1223405590579199) 1896112385589248) 0) := rfl
    _ = _ := by
      dsimp only [low, high]
      rw [hB]
      apply Int.ofNat_inj.mp
      norm_num [Nat.descFactorial]
      simp (disch := omega) only [Nat.cast_sub, Nat.cast_mul, Nat.cast_ofNat]
      ring

private theorem word18 (w : ℕ) :
    ([(false, 0), (true, 1896112385589248), (false, 1223405590579199), (true, 430197369060608), (false, 1583313975727487), (true, 1342499907841136), (false, 369012649234383), (true, 2141571347501048), (false, 24871845297935), (true, 2247491708383319), (false, 577924894832), (true, 2251739610991268), (false, 4853222763), (true, 2251799514034442), (false, 13896581), (true, 2251799813217068), (false, 10811), (true, 2251799813685095), (false, 0)] : List (Bool × ℕ)).foldr
      (fun s v => (((v <<< w) + (if s.1 then (2^w)-1 else 0)) <<< 51) + s.2) 0 =
      (2^(w+51)).descFactorial 18 := by
  rw [pow_add]
  simpa only [Nat.shiftLeft_eq] using falling18 (2^w) (2^51) (Nat.two_pow_pos _) rfl

set_option maxHeartbeats 2000000 in
private theorem certify18 (w : ℕ) (trace : List ℕ) :
    let ds : List (Bool × ℕ) := [(false, 0), (true, 1896112385589248), (false, 1223405590579199), (true, 430197369060608), (false, 1583313975727487), (true, 1342499907841136), (false, 369012649234383), (true, 2141571347501048), (false, 24871845297935), (true, 2247491708383319), (false, 577924894832), (true, 2251739610991268), (false, 4853222763), (true, 2251799514034442), (false, 13896581), (true, 2251799813217068), (false, 10811), (true, 2251799813685095), (false, 0)]
    let d : ℕ := 97692469875
    let t : ℕ := 51
    let cap := 4194304
    let fill (b : Bool) (j : ℕ) : ℕ := if b then 2^j-1 else 0
    let fold := Nat.rec (motive := fun _ => ℕ → ℕ) (fun v => (Nat.digits 2 v).count 1 % 2)
      (fun j f v => let base := 2^(8 * 2^j); f ((v / base) ^^^ (v % base)))
    let step (st : ℕ) (s : ℕ × ℕ) :=
      let v := ((st/2) <<< s.1) + s.2
      2*(v % d) + ((st % 2 + fold 19 (v / d)) % 2)
    let bits (s : Bool × ℕ) : List (ℕ × ℕ) :=
      List.replicate (w/cap) (cap, fill s.1 cap) ++ [(w%cap, fill s.1 (w%cap)),(t,s.2)]
    let chunks := ds.reverse.flatMap bits
    chunks.length = trace.length →
      ((chunks.zip trace).foldr (fun r f i => (step i r.1 == r.2) && f r.2)
        (fun i => i%2 == 0) 0) = true →
      (Nat.digits 2 ((2^(w+t)).descFactorial 18/d)).count 1 % 2 = 0 := by
  intro ds d t cap fill fold step bits chunks hlen cert
  have hc : ∀ s ∈ ds, s.2 < 2^t := by dsimp only [ds,t]; decide
  have h := verify_word_table ds w t d (by decide) hc trace
  rw [← word18 w]
  exact h hlen cert
private theorem modular_order18 : (2:ℕ)^3061800 % 97692469875 = 1 % 97692469875 := by
  have h0 : (2:ℕ)^0 ≡ 1 [MOD 97692469875] := by decide
  have h1 : (2:ℕ)^1 ≡ 2 [MOD 97692469875] :=
    extend_pow_mod (n := 0) (r := 1) (d := 97692469875) (m := 1) (s := 2) 1 h0 (by decide) (by decide)
  have h2 : (2:ℕ)^2 ≡ 4 [MOD 97692469875] :=
    extend_pow_mod (n := 1) (r := 2) (d := 97692469875) (m := 2) (s := 4) 0 h1 (by decide) (by decide)
  have h5 : (2:ℕ)^5 ≡ 32 [MOD 97692469875] :=
    extend_pow_mod (n := 2) (r := 4) (d := 97692469875) (m := 5) (s := 32) 1 h2 (by decide) (by decide)
  have h11 : (2:ℕ)^11 ≡ 2048 [MOD 97692469875] :=
    extend_pow_mod (n := 5) (r := 32) (d := 97692469875) (m := 11) (s := 2048) 1 h5 (by decide) (by decide)
  have h23 : (2:ℕ)^23 ≡ 8388608 [MOD 97692469875] :=
    extend_pow_mod (n := 11) (r := 2048) (d := 97692469875) (m := 23) (s := 8388608) 1 h11 (by decide) (by decide)
  have h46 : (2:ℕ)^46 ≡ 30165867664 [MOD 97692469875] :=
    extend_pow_mod (n := 23) (r := 8388608) (d := 97692469875) (m := 46) (s := 30165867664) 0 h23 (by decide) (by decide)
  have h93 : (2:ℕ)^93 ≡ 71361718667 [MOD 97692469875] :=
    extend_pow_mod (n := 46) (r := 30165867664) (d := 97692469875) (m := 93) (s := 71361718667) 1 h46 (by decide) (by decide)
  have h186 : (2:ℕ)^186 ≡ 78850596889 [MOD 97692469875] :=
    extend_pow_mod (n := 93) (r := 71361718667) (d := 97692469875) (m := 186) (s := 78850596889) 0 h93 (by decide) (by decide)
  have h373 : (2:ℕ)^373 ≡ 85367490392 [MOD 97692469875] :=
    extend_pow_mod (n := 186) (r := 78850596889) (d := 97692469875) (m := 373) (s := 85367490392) 1 h186 (by decide) (by decide)
  have h747 : (2:ℕ)^747 ≡ 39027422078 [MOD 97692469875] :=
    extend_pow_mod (n := 373) (r := 85367490392) (d := 97692469875) (m := 747) (s := 39027422078) 1 h373 (by decide) (by decide)
  have h1495 : (2:ℕ)^1495 ≡ 89023383668 [MOD 97692469875] :=
    extend_pow_mod (n := 747) (r := 39027422078) (d := 97692469875) (m := 1495) (s := 89023383668) 1 h747 (by decide) (by decide)
  have h2990 : (2:ℕ)^2990 ≡ 82484462974 [MOD 97692469875] :=
    extend_pow_mod (n := 1495) (r := 89023383668) (d := 97692469875) (m := 2990) (s := 82484462974) 0 h1495 (by decide) (by decide)
  have h5980 : (2:ℕ)^5980 ≡ 15987711301 [MOD 97692469875] :=
    extend_pow_mod (n := 2990) (r := 82484462974) (d := 97692469875) (m := 5980) (s := 15987711301) 0 h2990 (by decide) (by decide)
  have h11960 : (2:ℕ)^11960 ≡ 43669698601 [MOD 97692469875] :=
    extend_pow_mod (n := 5980) (r := 15987711301) (d := 97692469875) (m := 11960) (s := 43669698601) 0 h5980 (by decide) (by decide)
  have h23920 : (2:ℕ)^23920 ≡ 90133808326 [MOD 97692469875] :=
    extend_pow_mod (n := 11960) (r := 43669698601) (d := 97692469875) (m := 23920) (s := 90133808326) 0 h11960 (by decide) (by decide)
  have h47840 : (2:ℕ)^47840 ≡ 54769462276 [MOD 97692469875] :=
    extend_pow_mod (n := 23920) (r := 90133808326) (d := 97692469875) (m := 47840) (s := 54769462276) 0 h23920 (by decide) (by decide)
  have h95681 : (2:ℕ)^95681 ≡ 16302014852 [MOD 97692469875] :=
    extend_pow_mod (n := 47840) (r := 54769462276) (d := 97692469875) (m := 95681) (s := 16302014852) 1 h47840 (by decide) (by decide)
  have h191362 : (2:ℕ)^191362 ≡ 44498744404 [MOD 97692469875] :=
    extend_pow_mod (n := 95681) (r := 16302014852) (d := 97692469875) (m := 191362) (s := 44498744404) 0 h95681 (by decide) (by decide)
  have h382725 : (2:ℕ)^382725 ≡ 15094420307 [MOD 97692469875] :=
    extend_pow_mod (n := 191362) (r := 44498744404) (d := 97692469875) (m := 382725) (s := 15094420307) 1 h191362 (by decide) (by decide)
  have h765450 : (2:ℕ)^765450 ≡ 73599119749 [MOD 97692469875] :=
    extend_pow_mod (n := 382725) (r := 15094420307) (d := 97692469875) (m := 765450) (s := 73599119749) 0 h382725 (by decide) (by decide)
  have h1530900 : (2:ℕ)^1530900 ≡ 11493231751 [MOD 97692469875] :=
    extend_pow_mod (n := 765450) (r := 73599119749) (d := 97692469875) (m := 1530900) (s := 11493231751) 0 h765450 (by decide) (by decide)
  have h3061800 : (2:ℕ)^3061800 ≡ 1 [MOD 97692469875] :=
    extend_pow_mod (n := 1530900) (r := 11493231751) (d := 97692469875) (m := 3061800) (s := 1) 0 h1530900 (by decide) (by decide)
  exact h3061800

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
private theorem parity18_1656185 :
    (Nat.digits 2 ((2^1656185).descFactorial 18 / 97692469875)).count 1 % 2 = 0 := by
  let trace : List ℕ := [0, 0, 178377331867, 145414719209, 163426502272, 160374177829, 121884495468, 66903494950, 146662217050, 180786186313, 3845775774, 14400917087, 91394723825, 88044282878, 18279512919, 11811646700, 122555274800, 8060496315, 138417980642, 49062816855, 139813060137, 51507402849, 107343796899, 44957290550, 45570492200, 47272535117, 39981739211, 176521899853, 171741033019, 140894659439, 128016665458, 29715988050, 119444418450, 151966064248, 21709437748, 0, 0, 0]
  rw [show 1656185 = 1656134+51 by decide]
  apply certify18 1656134 trace
  · dsimp only [trace]; decide +kernel
  · dsimp only [trace]; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
private theorem parity18_2336585 :
    (Nat.digits 2 ((2^2336585).descFactorial 18 / 97692469875)).count 1 % 2 = 0 := by
  let trace : List ℕ := [0, 0, 4701829866, 123705281459, 185135940022, 138664740078, 56756182218, 132031808201, 124952779301, 7110684312, 177521277774, 36110354836, 26266410574, 153172596128, 61698388419, 163777710950, 35717523801, 94898247315, 73289667393, 114191130104, 96394184637, 94926278349, 194181547898, 153504479300, 45570492200, 47272535117, 39981739211, 176521899853, 171741033019, 140894659439, 128016665458, 29715988050, 119444418450, 151966064248, 21709437748, 0, 0, 0]
  rw [show 2336585 = 2336534+51 by decide]
  apply certify18 2336534 trace
  · dsimp only [trace]; decide +kernel
  · dsimp only [trace]; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
private theorem parity18_3357185 :
    (Nat.digits 2 ((2^3357185).descFactorial 18 / 97692469875)).count 1 % 2 = 0 := by
  let trace : List ℕ := [0, 0, 134958456366, 188833594708, 120007626772, 8408113578, 56756182219, 132031808200, 190081092551, 137367310812, 47264651274, 166366981337, 26266410574, 153172596128, 126826701668, 98649397700, 100845837050, 29769934064, 73289667393, 114191130104, 31265871386, 160054591599, 129053234648, 23247852801, 45570492200, 47272535117, 39981739210, 176521899852, 171741033019, 140894659439, 128016665458, 29715988050, 119444418450, 151966064248, 21709437748, 0, 0, 0]
  rw [show 3357185 = 3357134+51 by decide]
  apply certify18 3357134 trace
  · dsimp only [trace]; decide +kernel
  · dsimp only [trace]; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
private theorem parity18_3697385 :
    (Nat.digits 2 ((2^3697385).descFactorial 18 / 97692469875)).count 1 % 2 = 0 := by
  let trace : List ℕ := [0, 0, 48120705366, 80286405959, 33169875772, 95245864578, 121884495468, 66903494950, 81533903800, 50529559812, 134102402274, 79529230336, 91394723825, 88044282878, 148536139418, 76939959951, 57426961550, 73188809565, 138417980643, 49062816854, 9556433636, 181764029348, 172472110149, 175213917050, 45570492200, 47272535117, 39981739211, 176521899853, 171741033019, 140894659439, 128016665458, 29715988050, 119444418450, 151966064248, 21709437748, 0, 0, 0]
  rw [show 3697385 = 3697334+51 by decide]
  apply certify18 3697334 trace
  · dsimp only [trace]; decide +kernel
  · dsimp only [trace]; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
private theorem parity18_4037585 :
    (Nat.digits 2 ((2^4037585).descFactorial 18 / 97692469875)).count 1 % 2 = 0 := by
  let trace : List ℕ := [0, 0, 156667894116, 167124156958, 141717064522, 182083615578, 187012808719, 1775181701, 168371654800, 159076748562, 25555213524, 188076419086, 156523037074, 22915969629, 170245577168, 55230522200, 14008086051, 116607685064, 8161354143, 179319443354, 183231935636, 8088527348, 20506045899, 131795041550, 45570492200, 47272535117, 39981739210, 176521899852, 171741033019, 140894659439, 128016665458, 29715988050, 119444418450, 151966064248, 21709437748, 0, 0, 0]
  rw [show 4037585 = 4037534+51 by decide]
  apply certify18 4037534 trace
  · dsimp only [trace]; decide +kernel
  · dsimp only [trace]; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
private theorem parity18_4377785 :
    (Nat.digits 2 ((2^4377785).descFactorial 18 / 97692469875)).count 1 % 2 = 0 := by
  let trace : List ℕ := [0, 0, 0, 94328734531, 69830143116, 58576968208, 90842698078, 54879313522, 73536426829, 19304707279, 56756182219, 132031808200, 20675437450, 59824466050, 72238997562, 119106529273, 112392964524, 101238668087, 87856257376, 26266410575, 153172596129, 76637786078, 191955014919, 33521084451, 8909950701, 165974150301, 160026560565, 27260835555, 73289667392, 114191130105, 68375155664, 161522497887, 29797965099, 132310578848, 63924921398, 88376166051, 46139394050, 45570492200, 47272535117, 45361272887, 39981739211, 176521899853, 61880187132, 171741033019, 140894659439, 156708540539, 128016665458, 29715988050, 29773822051, 119444418450, 151966064248, 86837750998, 21709437748, 0, 0, 0, 0]
  rw [show 4377785 = 4377734+51 by decide]
  apply certify18 4377734 trace
  · dsimp only [trace]; decide +kernel
  · dsimp only [trace]; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
private theorem parity18_5058185 :
    (Nat.digits 2 ((2^5058185).descFactorial 18 / 97692469875)).count 1 % 2 = 0 := by
  let trace : List ℕ := [0, 0, 0, 94328734531, 91539580866, 36867530459, 134261573579, 76588751273, 51826989078, 62723582778, 187012808718, 1775181700, 85803750701, 38115028300, 93948435313, 75687653772, 90683526774, 122948105836, 44437381876, 156523037075, 22915969628, 141766099329, 39988950669, 185487148700, 95747701701, 79136399301, 51479371815, 48970273305, 8161354142, 179319443355, 133503468915, 118103622387, 73216840598, 45472827849, 150762672399, 1538415051, 24429956300, 45570492200, 47272535117, 45361272887, 39981739211, 176521899853, 61880187132, 171741033019, 140894659439, 156708540539, 128016665458, 29715988050, 29773822051, 119444418450, 151966064248, 86837750998, 21709437748, 0, 0, 0, 0]
  rw [show 5058185 = 5058134+51 by decide]
  apply certify18 5058134 trace
  · dsimp only [trace]; decide +kernel
  · dsimp only [trace]; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
private theorem parity18_5738585 :
    (Nat.digits 2 ((2^5738585).descFactorial 18 / 97692469875)).count 1 % 2 = 0 := by
  let trace : List ℕ := [0, 0, 0, 94328734531, 113249018617, 15158092709, 177680449079, 98298189022, 30117551328, 106142458279, 121884495468, 66903494950, 150932063951, 16405590551, 115657873063, 32268778273, 68974089025, 144657543587, 1018506376, 91394723824, 88044282879, 11509472829, 83407826168, 142068273201, 182585452701, 187683588051, 138317122815, 70679711054, 138417980643, 49062816854, 3246842414, 74684746886, 116635716099, 154020016598, 42215483649, 110085603800, 2720518550, 45570492200, 47272535117, 45361272887, 39981739211, 176521899853, 61880187132, 171741033019, 140894659439, 156708540539, 128016665458, 29715988050, 29773822051, 119444418450, 151966064248, 86837750998, 21709437748, 0, 0, 0, 0]
  rw [show 5738585 = 5738534+51 by decide]
  apply certify18 5738534 trace
  · dsimp only [trace]; decide +kernel
  · dsimp only [trace]; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
private theorem parity18_6078785 :
    (Nat.digits 2 ((2^6078785).descFactorial 18 / 97692469875)).count 1 % 2 = 0 := by
  let trace : List ℕ := [0, 0, 0, 94328734531, 26411267617, 101995843708, 4004947078, 11460438023, 116955302329, 127851896029, 187012808718, 1775181700, 85803750701, 103243341550, 28820122063, 10559340522, 155811840024, 57819792587, 174694008376, 156523037074, 22915969629, 141766099328, 105117263918, 120358835451, 30619388450, 144264712550, 181735998315, 179226899805, 8161354143, 179319443354, 133503468914, 52975309137, 138345153848, 110601141098, 85634359149, 66666728300, 89558269551, 45570492200, 47272535117, 45361272887, 39981739210, 176521899852, 61880187133, 171741033019, 140894659439, 156708540539, 128016665458, 29715988050, 29773822051, 119444418450, 151966064248, 86837750998, 21709437748, 0, 0, 0, 0]
  rw [show 6078785 = 6078734+51 by decide]
  apply certify18 6078734 trace
  · dsimp only [trace]; decide +kernel
  · dsimp only [trace]; decide +kernel

set_option maxHeartbeats 8000000 in
theorem col18 (a : ℕ) (ha : 51 ≤ a)
    (hr : a % 6123600 ∈ ([1656185, 2336585, 3357185, 3697385, 4037585, 4377785, 5058185, 5738585, 6078785] : List ℕ)) :
    OeisA249609.isEvil ((2^a).choose 18) = true := by
  let ds : List (Bool × ℕ) := [(false, 0), (true, 1896112385589248), (false, 1223405590579199), (true, 430197369060608), (false, 1583313975727487), (true, 1342499907841136), (false, 369012649234383), (true, 2141571347501048), (false, 24871845297935), (true, 2247491708383319), (false, 577924894832), (true, 2251739610991268), (false, 4853222763), (true, 2251799514034442), (false, 13896581), (true, 2251799813217068), (false, 10811), (true, 2251799813685095), (false, 0)]
  refine (periodic_column (k := 18) (t := 51) (l := 3061800) (d := 97692469875) (z := 16)
    (ds := ds) ha (by decide) modular_order18 ?_ ?_ (by decide)).2 ?_
  · dsimp only [ds]; decide
  · intro w
    rw [pow_add 2 w 51]
    exact falling18 (2^w) (2^51) (by positivity) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h | h | h | h | h | h
  · rw [show (a-51) % (3061800+3061800) + 51 = 1656185 by omega]
    exact parity18_1656185
  · rw [show (a-51) % (3061800+3061800) + 51 = 2336585 by omega]
    exact parity18_2336585
  · rw [show (a-51) % (3061800+3061800) + 51 = 3357185 by omega]
    exact parity18_3357185
  · rw [show (a-51) % (3061800+3061800) + 51 = 3697385 by omega]
    exact parity18_3697385
  · rw [show (a-51) % (3061800+3061800) + 51 = 4037585 by omega]
    exact parity18_4037585
  · rw [show (a-51) % (3061800+3061800) + 51 = 4377785 by omega]
    exact parity18_4377785
  · rw [show (a-51) % (3061800+3061800) + 51 = 5058185 by omega]
    exact parity18_5058185
  · rw [show (a-51) % (3061800+3061800) + 51 = 5738585 by omega]
    exact parity18_5738585
  · rw [show (a-51) % (3061800+3061800) + 51 = 6078785 by omega]
    exact parity18_6078785


set_option maxHeartbeats 8000000 in
private theorem falling19 (x B : ℕ) (hx : 0 < x) (hB : B = 36028797018963968) :
    ([(false, 0), (false, 6402373705728000), (true, 13651808960442368), (false, 34012249593822719), (true, 5707543011244544), (false, 17950712280921503), (true, 28477269426900944), (false, 2353125040549983), (true, 35470875337416920), (false, 102417740732657), (true, 36014086265555045), (false, 1661573386472), (true, 36028649458260236), (false, 10246937271), (true, 36028796469174686), (false, 22323821), (true, 36028797018301172), (false, 13565), (true, 36028797018963797), (false, 0)] : List (Bool × ℕ)).foldr
      (fun s v => (v * x + (if s.1 then x-1 else 0)) * B + s.2) 0 =
      (x * B).descFactorial 19 := by
  let low (v c : ℕ) := (v * x + 0) * B + c
  let high (v c : ℕ) := (v * x + (x-1)) * B + c
  calc
    _ = (low (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low 0 0) 36028797018963797) 13565) 36028797018301172) 22323821) 36028796469174686) 10246937271) 36028649458260236) 1661573386472) 36014086265555045) 102417740732657) 35470875337416920) 2353125040549983) 28477269426900944) 17950712280921503) 5707543011244544) 34012249593822719) 13651808960442368) 6402373705728000) 0) := rfl
    _ = _ := by
      dsimp only [low, high]
      rw [hB]
      apply Int.ofNat_inj.mp
      norm_num [Nat.descFactorial]
      simp (disch := omega) only [Nat.cast_sub, Nat.cast_mul, Nat.cast_ofNat]
      ring

private theorem word19 (w : ℕ) :
    ([(false, 0), (false, 6402373705728000), (true, 13651808960442368), (false, 34012249593822719), (true, 5707543011244544), (false, 17950712280921503), (true, 28477269426900944), (false, 2353125040549983), (true, 35470875337416920), (false, 102417740732657), (true, 36014086265555045), (false, 1661573386472), (true, 36028649458260236), (false, 10246937271), (true, 36028796469174686), (false, 22323821), (true, 36028797018301172), (false, 13565), (true, 36028797018963797), (false, 0)] : List (Bool × ℕ)).foldr
      (fun s v => (((v <<< w) + (if s.1 then (2^w)-1 else 0)) <<< 55) + s.2) 0 =
      (2^(w+55)).descFactorial 19 := by
  rw [pow_add]
  simpa only [Nat.shiftLeft_eq] using falling19 (2^w) (2^55) (Nat.two_pow_pos _) rfl

set_option maxHeartbeats 2000000 in
private theorem certify19 (w : ℕ) (trace : List ℕ) :
    let ds : List (Bool × ℕ) := [(false, 0), (false, 6402373705728000), (true, 13651808960442368), (false, 34012249593822719), (true, 5707543011244544), (false, 17950712280921503), (true, 28477269426900944), (false, 2353125040549983), (true, 35470875337416920), (false, 102417740732657), (true, 36014086265555045), (false, 1661573386472), (true, 36028649458260236), (false, 10246937271), (true, 36028796469174686), (false, 22323821), (true, 36028797018301172), (false, 13565), (true, 36028797018963797), (false, 0)]
    let d : ℕ := 1856156927625
    let t : ℕ := 55
    let cap := 4194304
    let fill (b : Bool) (j : ℕ) : ℕ := if b then 2^j-1 else 0
    let fold := Nat.rec (motive := fun _ => ℕ → ℕ) (fun v => (Nat.digits 2 v).count 1 % 2)
      (fun j f v => let base := 2^(8 * 2^j); f ((v / base) ^^^ (v % base)))
    let step (st : ℕ) (s : ℕ × ℕ) :=
      let v := ((st/2) <<< s.1) + s.2
      2*(v % d) + ((st % 2 + fold 19 (v / d)) % 2)
    let bits (s : Bool × ℕ) : List (ℕ × ℕ) :=
      List.replicate (w/cap) (cap, fill s.1 cap) ++ [(w%cap, fill s.1 (w%cap)),(t,s.2)]
    let chunks := ds.reverse.flatMap bits
    chunks.length = trace.length →
      ((chunks.zip trace).foldr (fun r f i => (step i r.1 == r.2) && f r.2)
        (fun i => i%2 == 0) 0) = true →
      (Nat.digits 2 ((2^(w+t)).descFactorial 19/d)).count 1 % 2 = 0 := by
  intro ds d t cap fill fold step bits chunks hlen cert
  have hc : ∀ s ∈ ds, s.2 < 2^t := by dsimp only [ds,t]; decide
  have h := verify_word_table ds w t d (by decide) hc trace
  rw [← word19 w]
  exact h hlen cert
private theorem modular_order19 : (2:ℕ)^3061800 % 1856156927625 = 1 % 1856156927625 := by
  have h0 : (2:ℕ)^0 ≡ 1 [MOD 1856156927625] := by decide
  have h1 : (2:ℕ)^1 ≡ 2 [MOD 1856156927625] :=
    extend_pow_mod (n := 0) (r := 1) (d := 1856156927625) (m := 1) (s := 2) 1 h0 (by decide) (by decide)
  have h2 : (2:ℕ)^2 ≡ 4 [MOD 1856156927625] :=
    extend_pow_mod (n := 1) (r := 2) (d := 1856156927625) (m := 2) (s := 4) 0 h1 (by decide) (by decide)
  have h5 : (2:ℕ)^5 ≡ 32 [MOD 1856156927625] :=
    extend_pow_mod (n := 2) (r := 4) (d := 1856156927625) (m := 5) (s := 32) 1 h2 (by decide) (by decide)
  have h11 : (2:ℕ)^11 ≡ 2048 [MOD 1856156927625] :=
    extend_pow_mod (n := 5) (r := 32) (d := 1856156927625) (m := 11) (s := 2048) 1 h5 (by decide) (by decide)
  have h23 : (2:ℕ)^23 ≡ 8388608 [MOD 1856156927625] :=
    extend_pow_mod (n := 11) (r := 2048) (d := 1856156927625) (m := 23) (s := 8388608) 1 h11 (by decide) (by decide)
  have h46 : (2:ℕ)^46 ≡ 1690937855539 [MOD 1856156927625] :=
    extend_pow_mod (n := 23) (r := 8388608) (d := 1856156927625) (m := 46) (s := 1690937855539) 0 h23 (by decide) (by decide)
  have h93 : (2:ℕ)^93 ≡ 266746658417 [MOD 1856156927625] :=
    extend_pow_mod (n := 46) (r := 1690937855539) (d := 1856156927625) (m := 93) (s := 266746658417) 1 h46 (by decide) (by decide)
  have h186 : (2:ℕ)^186 ≡ 469620476389 [MOD 1856156927625] :=
    extend_pow_mod (n := 93) (r := 266746658417) (d := 1856156927625) (m := 186) (s := 469620476389) 0 h93 (by decide) (by decide)
  have h373 : (2:ℕ)^373 ≡ 1453062068642 [MOD 1856156927625] :=
    extend_pow_mod (n := 186) (r := 469620476389) (d := 1856156927625) (m := 373) (s := 1453062068642) 1 h186 (by decide) (by decide)
  have h747 : (2:ℕ)^747 ≡ 625182241328 [MOD 1856156927625] :=
    extend_pow_mod (n := 373) (r := 1453062068642) (d := 1856156927625) (m := 747) (s := 625182241328) 1 h373 (by decide) (by decide)
  have h1495 : (2:ℕ)^1495 ≡ 1749795371543 [MOD 1856156927625] :=
    extend_pow_mod (n := 747) (r := 625182241328) (d := 1856156927625) (m := 1495) (s := 1749795371543) 1 h747 (by decide) (by decide)
  have h2990 : (2:ℕ)^2990 ≡ 1352486571349 [MOD 1856156927625] :=
    extend_pow_mod (n := 1495) (r := 1749795371543) (d := 1856156927625) (m := 2990) (s := 1352486571349) 0 h1495 (by decide) (by decide)
  have h5980 : (2:ℕ)^5980 ≡ 797527470301 [MOD 1856156927625] :=
    extend_pow_mod (n := 2990) (r := 1352486571349) (d := 1856156927625) (m := 5980) (s := 797527470301) 0 h2990 (by decide) (by decide)
  have h11960 : (2:ℕ)^11960 ≡ 532132047976 [MOD 1856156927625] :=
    extend_pow_mod (n := 5980) (r := 797527470301) (d := 1856156927625) (m := 11960) (s := 532132047976) 0 h5980 (by decide) (by decide)
  have h23920 : (2:ℕ)^23920 ≡ 773981097451 [MOD 1856156927625] :=
    extend_pow_mod (n := 11960) (r := 532132047976) (d := 1856156927625) (m := 23920) (s := 773981097451) 0 h11960 (by decide) (by decide)
  have h47840 : (2:ℕ)^47840 ≡ 1617848980276 [MOD 1856156927625] :=
    extend_pow_mod (n := 23920) (r := 773981097451) (d := 1856156927625) (m := 47840) (s := 1617848980276) 0 h23920 (by decide) (by decide)
  have h95681 : (2:ℕ)^95681 ≡ 895534243727 [MOD 1856156927625] :=
    extend_pow_mod (n := 47840) (r := 1617848980276) (d := 1856156927625) (m := 95681) (s := 895534243727) 1 h47840 (by decide) (by decide)
  have h191362 : (2:ℕ)^191362 ≡ 1119115913029 [MOD 1856156927625] :=
    extend_pow_mod (n := 95681) (r := 895534243727) (d := 1856156927625) (m := 191362) (s := 1119115913029) 0 h95681 (by decide) (by decide)
  have h382725 : (2:ℕ)^382725 ≡ 992019119057 [MOD 1856156927625] :=
    extend_pow_mod (n := 191362) (r := 1119115913029) (d := 1856156927625) (m := 382725) (s := 992019119057) 1 h191362 (by decide) (by decide)
  have h765450 : (2:ℕ)^765450 ≡ 757446408874 [MOD 1856156927625] :=
    extend_pow_mod (n := 382725) (r := 992019119057) (d := 1856156927625) (m := 765450) (s := 757446408874) 0 h382725 (by decide) (by decide)
  have h1530900 : (2:ℕ)^1530900 ≡ 109185701626 [MOD 1856156927625] :=
    extend_pow_mod (n := 765450) (r := 757446408874) (d := 1856156927625) (m := 1530900) (s := 109185701626) 0 h765450 (by decide) (by decide)
  have h3061800 : (2:ℕ)^3061800 ≡ 1 [MOD 1856156927625] :=
    extend_pow_mod (n := 1530900) (r := 109185701626) (d := 1856156927625) (m := 3061800) (s := 1) 0 h1530900 (by decide) (by decide)
  exact h3061800

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
private theorem parity19_295385 :
    (Nat.digits 2 ((2^295385).descFactorial 19 / 1856156927625)).count 1 % 2 = 0 := by
  let trace : List ℕ := [0, 0, 1864591831147, 1361143233172, 3201639306479, 1103257023085, 967578967363, 566840583010, 2524668256241, 691568859462, 375267630834, 1796839121434, 1792414286867, 3215500064331, 1455975563816, 76931823861, 2831031597891, 3138704269214, 3444692629233, 2509106413166, 981908851034, 58463647226, 2305299440121, 3394583276001, 2812860480500, 1191890702716, 3346045383131, 497925906229, 3543741067123, 3020433594353, 2940951415445, 2964390431131, 2317969833121, 3329392134599, 2761121289149, 781539759001, 1367694578250, 0, 0, 0]
  rw [show 295385 = 295330+55 by decide]
  apply certify19 295330 trace
  · dsimp only [trace]; decide +kernel
  · dsimp only [trace]; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
private theorem parity19_635585 :
    (Nat.digits 2 ((2^635585).descFactorial 19 / 1856156927625)).count 1 % 2 = 0 := by
  let trace : List ℕ := [0, 0, 2689550465647, 3011060502172, 314284085729, 2753174292084, 2205016919113, 3041716486511, 1699709621740, 2753965445713, 3262622851585, 146921852434, 3029852238617, 1978062112580, 3105892832816, 3376766361861, 3243510915141, 251349048464, 969816725733, 1271668461417, 3044305437285, 470942964476, 1892820122871, 2569624641500, 2812860480500, 1191890702716, 3346045383131, 497925906229, 3543741067122, 3020433594352, 2940951415444, 2964390431130, 2317969833121, 3329392134599, 2761121289149, 781539759001, 1367694578250, 0, 0, 0]
  rw [show 635585 = 635530+55 by decide]
  apply certify19 635530 trace
  · dsimp only [trace]; decide +kernel
  · dsimp only [trace]; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
private theorem parity19_975785 :
    (Nat.digits 2 ((2^975785).descFactorial 19 / 1856156927625)).count 1 % 2 = 0 := by
  let trace : List ℕ := [0, 0, 3514509100147, 948663915923, 1139242720228, 690777705834, 3442454870863, 1804278534761, 874750987241, 1104048176712, 2437664217085, 2209318438684, 554976335116, 740624160830, 1043496246566, 2964287044611, 3655990232390, 1076307682965, 2207254677483, 34230509667, 1394388168284, 883422281727, 1480340805621, 1744666007000, 2812860480500, 1191890702716, 3346045383131, 497925906229, 3543741067123, 3020433594353, 2940951415445, 2964390431131, 2317969833121, 3329392134599, 2761121289149, 781539759001, 1367694578250, 0, 0, 0]
  rw [show 975785 = 975730+55 by decide]
  apply certify19 975730 trace
  · dsimp only [trace]; decide +kernel
  · dsimp only [trace]; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
private theorem parity19_1315985 :
    (Nat.digits 2 ((2^1315985).descFactorial 19 / 1856156927625)).count 1 % 2 = 0 := by
  let trace : List ℕ := [0, 0, 627153879397, 2598581184923, 1964201354728, 2340694974834, 967578967363, 566840583010, 49792352741, 3166444762963, 1612705582584, 559401169685, 1792414286867, 3215500064331, 2693413515566, 2551807727360, 356155694390, 1901266317465, 3444692629232, 2509106413167, 3456784754534, 1295901598977, 1067861488371, 919707372500, 2812860480500, 1191890702716, 3346045383131, 497925906229, 3543741067122, 3020433594352, 2940951415444, 2964390431130, 2317969833121, 3329392134599, 2761121289149, 781539759001, 1367694578250, 0, 0, 0]
  rw [show 1315985 = 1315930+55 by decide]
  apply certify19 1315930 trace
  · dsimp only [trace]; decide +kernel
  · dsimp only [trace]; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
private theorem parity19_2676785 :
    (Nat.digits 2 ((2^2676785).descFactorial 19 / 1856156927625)).count 1 % 2 = 0 := by
  let trace : List ℕ := [0, 0, 214674562147, 1773622550422, 1551722037479, 1515736340334, 2205016919113, 3041716486511, 462271669990, 279089542212, 2025184899834, 1384359804185, 3029852238617, 1978062112580, 1868454881066, 901890458361, 2006072963390, 1488787000214, 969816725732, 1271668461416, 569429533784, 2945818867977, 3130258074620, 1332186689751, 2812860480500, 1191890702716, 3346045383131, 497925906229, 3543741067122, 3020433594352, 2940951415444, 2964390431130, 2317969833121, 3329392134599, 2761121289149, 781539759001, 1367694578250, 0, 0, 0]
  rw [show 2676785 = 2676730+55 by decide]
  apply certify19 2676730 trace
  · dsimp only [trace]; decide +kernel
  · dsimp only [trace]; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
private theorem parity19_4717985 :
    (Nat.digits 2 ((2^4717985).descFactorial 19 / 1856156927625)).count 1 % 2 = 0 := by
  let trace : List ℕ := [0, 0, 0, 94328734531, 1452112513896, 536184598673, 368484311752, 2789159989229, 278298388584, 2508929314374, 2205016919113, 3041716486511, 3711146127911, 2937147573491, 1516527493962, 702163916172, 787746948084, 2621797755935, 2806852786444, 3029852238616, 1978062112581, 383946237561, 631016929317, 2139328410111, 3557472170511, 768635011641, 2726224951964, 1929278309205, 969816725732, 1271668461416, 489476501157, 1806867485534, 1708380916227, 2961222636146, 655382171121, 94748738000, 1072930701501, 2812860480500, 1191890702716, 2927166035237, 3346045383131, 497925906229, 2762306190649, 3543741067122, 3020433594352, 3145948906912, 2940951415444, 2964390431130, 335179128331, 2317969833121, 3329392134599, 3458607749099, 2761121289149, 781539759001, 195384939750, 1367694578250, 0, 0, 0, 0]
  rw [show 4717985 = 4717930+55 by decide]
  apply certify19 4717930 trace
  · dsimp only [trace]; decide +kernel
  · dsimp only [trace]; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
private theorem parity19_5398385 :
    (Nat.digits 2 ((2^5398385).descFactorial 19 / 1856156927625)).count 1 % 2 = 0 := by
  let trace : List ℕ := [0, 0, 0, 94328734531, 3102029782897, 123705281422, 1193442946253, 726763402978, 3578132926585, 3333887948875, 967578967362, 566840583011, 1236270224411, 1287230304490, 1929006811213, 3589519136923, 2850143534335, 3034277073184, 1981894151944, 1792414286867, 3215500064331, 1621384189311, 218537612067, 1314369775611, 1495075584260, 1593593646140, 663828365714, 2341757626454, 3444692629232, 2509106413167, 1726914452907, 2219346802785, 2533339550726, 1311305367146, 3542737391870, 2157145324250, 660451384250, 2812860480500, 1191890702716, 2927166035237, 3346045383131, 497925906229, 2762306190649, 3543741067122, 3020433594352, 3145948906912, 2940951415444, 2964390431130, 335179128331, 2317969833121, 3329392134599, 3458607749099, 2761121289149, 781539759001, 195384939750, 1367694578250, 0, 0, 0, 0]
  rw [show 5398385 = 5398330+55 by decide]
  apply certify19 5398330 trace
  · dsimp only [trace]; decide +kernel
  · dsimp only [trace]; decide +kernel

set_option maxHeartbeats 8000000 in
theorem col19 (a : ℕ) (ha : 55 ≤ a)
    (hr : a % 6123600 ∈ ([295385, 635585, 975785, 1315985, 2676785, 4717985, 5398385] : List ℕ)) :
    OeisA249609.isEvil ((2^a).choose 19) = true := by
  let ds : List (Bool × ℕ) := [(false, 0), (false, 6402373705728000), (true, 13651808960442368), (false, 34012249593822719), (true, 5707543011244544), (false, 17950712280921503), (true, 28477269426900944), (false, 2353125040549983), (true, 35470875337416920), (false, 102417740732657), (true, 36014086265555045), (false, 1661573386472), (true, 36028649458260236), (false, 10246937271), (true, 36028796469174686), (false, 22323821), (true, 36028797018301172), (false, 13565), (true, 36028797018963797), (false, 0)]
  refine (periodic_column (k := 19) (t := 55) (l := 3061800) (d := 1856156927625) (z := 16)
    (ds := ds) ha (by decide) modular_order19 ?_ ?_ (by decide)).2 ?_
  · dsimp only [ds]; decide
  · intro w
    rw [pow_add 2 w 55]
    exact falling19 (2^w) (2^55) (by positivity) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h | h | h | h
  · rw [show (a-55) % (3061800+3061800) + 55 = 295385 by omega]
    exact parity19_295385
  · rw [show (a-55) % (3061800+3061800) + 55 = 635585 by omega]
    exact parity19_635585
  · rw [show (a-55) % (3061800+3061800) + 55 = 975785 by omega]
    exact parity19_975785
  · rw [show (a-55) % (3061800+3061800) + 55 = 1315985 by omega]
    exact parity19_1315985
  · rw [show (a-55) % (3061800+3061800) + 55 = 2676785 by omega]
    exact parity19_2676785
  · rw [show (a-55) % (3061800+3061800) + 55 = 4717985 by omega]
    exact parity19_4717985
  · rw [show (a-55) % (3061800+3061800) + 55 = 5398385 by omega]
    exact parity19_5398385


set_option maxHeartbeats 8000000 in
private theorem falling20 (x B : ℕ) (hx : 0 < x) (hB : B = 1152921504606846976) :
    ([(false, 0), (true, 1031276404198014976), (false, 431565146817638399), (true, 484311774265693696), (false, 610116075740491775), (true, 781536717261618976), (false, 161429736530118959), (true, 1100660601244334256), (false, 12953636989943895), (true, 1150417645851379426), (false, 381922055502194), (true, 1152875223959095066), (false, 4465226757380), (true, 1152921162354335076), (false, 20692933629), (true, 1152921503632905076), (false, 34916945), (true, 1152921504605926426), (false, 16814), (true, 1152921504606846786), (false, 0)] : List (Bool × ℕ)).foldr
      (fun s v => (v * x + (if s.1 then x-1 else 0)) * B + s.2) 0 =
      (x * B).descFactorial 20 := by
  let low (v c : ℕ) := (v * x + 0) * B + c
  let high (v c : ℕ) := (v * x + (x-1)) * B + c
  calc
    _ = (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low 0 0) 1152921504606846786) 16814) 1152921504605926426) 34916945) 1152921503632905076) 20692933629) 1152921162354335076) 4465226757380) 1152875223959095066) 381922055502194) 1150417645851379426) 12953636989943895) 1100660601244334256) 161429736530118959) 781536717261618976) 610116075740491775) 484311774265693696) 431565146817638399) 1031276404198014976) 0) := rfl
    _ = _ := by
      dsimp only [low, high]
      rw [hB]
      apply Int.ofNat_inj.mp
      norm_num [Nat.descFactorial]
      simp (disch := omega) only [Nat.cast_sub, Nat.cast_mul, Nat.cast_ofNat]
      ring

private theorem word20 (w : ℕ) :
    ([(false, 0), (true, 1031276404198014976), (false, 431565146817638399), (true, 484311774265693696), (false, 610116075740491775), (true, 781536717261618976), (false, 161429736530118959), (true, 1100660601244334256), (false, 12953636989943895), (true, 1150417645851379426), (false, 381922055502194), (true, 1152875223959095066), (false, 4465226757380), (true, 1152921162354335076), (false, 20692933629), (true, 1152921503632905076), (false, 34916945), (true, 1152921504605926426), (false, 16814), (true, 1152921504606846786), (false, 0)] : List (Bool × ℕ)).foldr
      (fun s v => (((v <<< w) + (if s.1 then (2^w)-1 else 0)) <<< 60) + s.2) 0 =
      (2^(w+60)).descFactorial 20 := by
  rw [pow_add]
  simpa only [Nat.shiftLeft_eq] using falling20 (2^w) (2^60) (Nat.two_pow_pos _) rfl

set_option maxHeartbeats 2000000 in
private theorem certify20 (w : ℕ) (trace : List ℕ) :
    let ds : List (Bool × ℕ) := [(false, 0), (true, 1031276404198014976), (false, 431565146817638399), (true, 484311774265693696), (false, 610116075740491775), (true, 781536717261618976), (false, 161429736530118959), (true, 1100660601244334256), (false, 12953636989943895), (true, 1150417645851379426), (false, 381922055502194), (true, 1152875223959095066), (false, 4465226757380), (true, 1152921162354335076), (false, 20692933629), (true, 1152921503632905076), (false, 34916945), (true, 1152921504605926426), (false, 16814), (true, 1152921504606846786), (false, 0)]
    let d : ℕ := 9280784638125
    let t : ℕ := 60
    let cap := 4194304
    let fill (b : Bool) (j : ℕ) : ℕ := if b then 2^j-1 else 0
    let fold := Nat.rec (motive := fun _ => ℕ → ℕ) (fun v => (Nat.digits 2 v).count 1 % 2)
      (fun j f v => let base := 2^(8 * 2^j); f ((v / base) ^^^ (v % base)))
    let step (st : ℕ) (s : ℕ × ℕ) :=
      let v := ((st/2) <<< s.1) + s.2
      2*(v % d) + ((st % 2 + fold 19 (v / d)) % 2)
    let bits (s : Bool × ℕ) : List (ℕ × ℕ) :=
      List.replicate (w/cap) (cap, fill s.1 cap) ++ [(w%cap, fill s.1 (w%cap)),(t,s.2)]
    let chunks := ds.reverse.flatMap bits
    chunks.length = trace.length →
      ((chunks.zip trace).foldr (fun r f i => (step i r.1 == r.2) && f r.2)
        (fun i => i%2 == 0) 0) = true →
      (Nat.digits 2 ((2^(w+t)).descFactorial 20/d)).count 1 % 2 = 0 := by
  intro ds d t cap fill fold step bits chunks hlen cert
  have hc : ∀ s ∈ ds, s.2 < 2^t := by dsimp only [ds,t]; decide
  have h := verify_word_table ds w t d (by decide) hc trace
  rw [← word20 w]
  exact h hlen cert
private theorem modular_order20 : (2:ℕ)^15309000 % 9280784638125 = 1 % 9280784638125 := by
  have h0 : (2:ℕ)^0 ≡ 1 [MOD 9280784638125] := by decide
  have h1 : (2:ℕ)^1 ≡ 2 [MOD 9280784638125] :=
    extend_pow_mod (n := 0) (r := 1) (d := 9280784638125) (m := 1) (s := 2) 1 h0 (by decide) (by decide)
  have h3 : (2:ℕ)^3 ≡ 8 [MOD 9280784638125] :=
    extend_pow_mod (n := 1) (r := 2) (d := 9280784638125) (m := 3) (s := 8) 1 h1 (by decide) (by decide)
  have h7 : (2:ℕ)^7 ≡ 128 [MOD 9280784638125] :=
    extend_pow_mod (n := 3) (r := 8) (d := 9280784638125) (m := 7) (s := 128) 1 h3 (by decide) (by decide)
  have h14 : (2:ℕ)^14 ≡ 16384 [MOD 9280784638125] :=
    extend_pow_mod (n := 7) (r := 128) (d := 9280784638125) (m := 14) (s := 16384) 0 h7 (by decide) (by decide)
  have h29 : (2:ℕ)^29 ≡ 536870912 [MOD 9280784638125] :=
    extend_pow_mod (n := 14) (r := 16384) (d := 9280784638125) (m := 29) (s := 536870912) 1 h14 (by decide) (by decide)
  have h58 : (2:ℕ)^58 ≡ 6328430101744 [MOD 9280784638125] :=
    extend_pow_mod (n := 29) (r := 536870912) (d := 9280784638125) (m := 58) (s := 6328430101744) 0 h29 (by decide) (by decide)
  have h116 : (2:ℕ)^116 ≡ 6278007334036 [MOD 9280784638125] :=
    extend_pow_mod (n := 58) (r := 6328430101744) (d := 9280784638125) (m := 116) (s := 6278007334036) 0 h58 (by decide) (by decide)
  have h233 : (2:ℕ)^233 ≡ 6344777226092 [MOD 9280784638125] :=
    extend_pow_mod (n := 116) (r := 6278007334036) (d := 9280784638125) (m := 233) (s := 6344777226092) 1 h116 (by decide) (by decide)
  have h467 : (2:ℕ)^467 ≡ 7981151742428 [MOD 9280784638125] :=
    extend_pow_mod (n := 233) (r := 6344777226092) (d := 9280784638125) (m := 467) (s := 7981151742428) 1 h233 (by decide) (by decide)
  have h934 : (2:ℕ)^934 ≡ 4972644508309 [MOD 9280784638125] :=
    extend_pow_mod (n := 467) (r := 7981151742428) (d := 9280784638125) (m := 934) (s := 4972644508309) 0 h467 (by decide) (by decide)
  have h1868 : (2:ℕ)^1868 ≡ 1799872299481 [MOD 9280784638125] :=
    extend_pow_mod (n := 934) (r := 4972644508309) (d := 9280784638125) (m := 1868) (s := 1799872299481) 0 h934 (by decide) (by decide)
  have h3737 : (2:ℕ)^3737 ≡ 3279875004347 [MOD 9280784638125] :=
    extend_pow_mod (n := 1868) (r := 1799872299481) (d := 9280784638125) (m := 3737) (s := 3279875004347) 1 h1868 (by decide) (by decide)
  have h7475 : (2:ℕ)^7475 ≡ 2914118570318 [MOD 9280784638125] :=
    extend_pow_mod (n := 3737) (r := 3279875004347) (d := 9280784638125) (m := 7475) (s := 2914118570318) 1 h3737 (by decide) (by decide)
  have h14950 : (2:ℕ)^14950 ≡ 3566129542999 [MOD 9280784638125] :=
    extend_pow_mod (n := 7475) (r := 2914118570318) (d := 9280784638125) (m := 14950) (s := 3566129542999) 0 h7475 (by decide) (by decide)
  have h29900 : (2:ℕ)^29900 ≡ 1942800457126 [MOD 9280784638125] :=
    extend_pow_mod (n := 14950) (r := 3566129542999) (d := 9280784638125) (m := 29900) (s := 1942800457126) 0 h14950 (by decide) (by decide)
  have h59800 : (2:ℕ)^59800 ≡ 9093535390501 [MOD 9280784638125] :=
    extend_pow_mod (n := 29900) (r := 1942800457126) (d := 9280784638125) (m := 59800) (s := 9093535390501) 0 h29900 (by decide) (by decide)
  have h119601 : (2:ℕ)^119601 ≡ 8135774592002 [MOD 9280784638125] :=
    extend_pow_mod (n := 59800) (r := 9093535390501) (d := 9280784638125) (m := 119601) (s := 8135774592002) 1 h59800 (by decide) (by decide)
  have h239203 : (2:ℕ)^239203 ≡ 6908995359758 [MOD 9280784638125] :=
    extend_pow_mod (n := 119601) (r := 8135774592002) (d := 9280784638125) (m := 239203) (s := 6908995359758) 1 h119601 (by decide) (by decide)
  have h478406 : (2:ℕ)^478406 ≡ 1146199296064 [MOD 9280784638125] :=
    extend_pow_mod (n := 239203) (r := 6908995359758) (d := 9280784638125) (m := 478406) (s := 1146199296064) 0 h239203 (by decide) (by decide)
  have h956812 : (2:ℕ)^956812 ≡ 9260472164596 [MOD 9280784638125] :=
    extend_pow_mod (n := 478406) (r := 1146199296064) (d := 9280784638125) (m := 956812) (s := 9260472164596) 0 h478406 (by decide) (by decide)
  have h1913625 : (2:ℕ)^1913625 ≡ 773647715807 [MOD 9280784638125] :=
    extend_pow_mod (n := 956812) (r := 9260472164596) (d := 9280784638125) (m := 1913625) (s := 773647715807) 1 h956812 (by decide) (by decide)
  have h3827250 : (2:ℕ)^3827250 ≡ 8182074119374 [MOD 9280784638125] :=
    extend_pow_mod (n := 1913625) (r := 773647715807) (d := 9280784638125) (m := 3827250) (s := 8182074119374) 0 h1913625 (by decide) (by decide)
  have h7654500 : (2:ℕ)^7654500 ≡ 3821499556876 [MOD 9280784638125] :=
    extend_pow_mod (n := 3827250) (r := 8182074119374) (d := 9280784638125) (m := 7654500) (s := 3821499556876) 0 h3827250 (by decide) (by decide)
  have h15309000 : (2:ℕ)^15309000 ≡ 1 [MOD 9280784638125] :=
    extend_pow_mod (n := 7654500) (r := 3821499556876) (d := 9280784638125) (m := 15309000) (s := 1) 0 h7654500 (by decide) (by decide)
  exact h15309000

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
private theorem parity20_1996385 :
    (Nat.digits 2 ((2^1996385).descFactorial 20 / 9280784638125)).count 1 % 2 = 0 := by
  let trace : List ℕ := [0, 0, 11324109847113, 9610729578134, 1197136180138, 8652360290067, 16523263058124, 6003633448377, 8346921234682, 17557712038022, 13129941141367, 10930913923119, 5259878808226, 4548778040584, 11226732984401, 6216559313302, 1466840533964, 15288817085124, 7836406058181, 17944961037562, 2290651276784, 16319735970823, 16735823679716, 18370467351418, 7136286415076, 3928937170466, 5859055718424, 11262827251836, 6592743444402, 15833724507521, 18405534677003, 8685487677655, 4938805709028, 17539937192879, 7178706434158, 4344738596101, 17892972430201, 11136941565749, 3712313855248, 0, 0, 0]
  rw [show 1996385 = 1996325+60 by decide]
  apply certify20 1996325 trace
  · dsimp only [trace]; decide +kernel
  · dsimp only [trace]; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
private theorem parity20_9140585 :
    (Nat.digits 2 ((2^9140585).descFactorial 20 / 9280784638125)).count 1 % 2 = 0 := by
  let trace : List ℕ := [0, 0, 0, 0, 3806642589780, 18108849008760, 12561547798863, 10848167529884, 7650783335144, 491004383054, 12334077745888, 1227732579567, 10356982812087, 2385613544906, 436569685375, 8478509351877, 12551155618016, 6837924860006, 10821797138183, 1471018665273, 7736499128882, 5646011857893, 1992999575616, 18355541633619, 11739621510639, 11167632097958, 6497316759977, 5786215992335, 10575558151625, 12486661472764, 17413922743151, 12403749072053, 15649021567583, 8719555214813, 8891468244465, 4151875519375, 17245649836765, 12262537182504, 1649216299431, 11757771278813, 10030872158243, 15909979746622, 3528089228534, 17557173922573, 13872655659432, 3031463986693, 9311195969217, 10945839640919, 10393912057438, 1752023235509, 9611162318577, 6403813073966, 1928010617486, 1452633960056, 9571369573675, 14975141107087, 6543173205126, 10230940066267, 17729685010152, 8409096797021, 6346839113350, 12577602623381, 10980906966502, 1260859967155, 7383799291464, 7286196815424, 4938805709029, 17539937192878, 802518166079, 18219305548528, 7178706434158, 4344738596101, 1303487101350, 7351246315351, 17892972430201, 11136941565749, 11136941565749, 11136941565749, 3712313855248, 0, 0, 0, 0, 0]
  rw [show 9140585 = 9140525+60 by decide]
  apply certify20 9140525 trace
  · dsimp only [trace]; decide +kernel
  · dsimp only [trace]; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
private theorem parity20_15264185 :
    (Nat.digits 2 ((2^15264185).descFactorial 20 / 9280784638125)).count 1 % 2 = 0 := by
  let trace : List ℕ := [0, 0, 0, 0, 0, 3806642589780, 18108849008760, 5335913591191, 16273861654113, 14560481385134, 11363097190395, 4203318238304, 6344272091114, 8621763890638, 16076988000566, 6644668956836, 17234868965906, 706869947276, 7861197395874, 15903137062376, 1414214052267, 14262552570506, 10829792733596, 18246424848682, 8895646375772, 15161126839382, 13070639568392, 3020218483802, 5705313430866, 3506286212618, 15451935365888, 14879945953208, 9362436040328, 10209630615226, 9498529847585, 14287872006874, 16198975328014, 12629061262505, 17413922743150, 12403749072052, 15649021567582, 8719555214812, 9456427907993, 12603782099714, 7864189374625, 2396394415765, 15974851037755, 11523959777095, 1649216299431, 11757771278813, 10030872158243, 15909979746622, 8014857175703, 7240403083784, 2707918501572, 17584969514683, 6743777841943, 5148221646853, 5598882113967, 7233525785669, 6681598202189, 16601278656508, 17074466059379, 17035790029076, 13828440784466, 9352638327986, 8877261670556, 18540001666677, 2146741863175, 7550513396587, 17680114770876, 2806312355767, 12933333714006, 14017371154902, 4696782941770, 2634525258101, 8865288768130, 11635203202361, 7268593111252, 16110115388155, 3671485436214, 3573882960174, 14619223979785, 4938805709029, 17539937192878, 802518166079, 18219305548528, 10881568052729, 7178706434158, 4344738596101, 1303487101350, 7351246315351, 6422923864351, 17892972430201, 11136941565749, 11136941565749, 11136941565749, 11136941565749, 3712313855248, 0, 0, 0, 0, 0, 0]
  rw [show 15264185 = 15264125+60 by decide]
  apply certify20 15264125 trace
  · dsimp only [trace]; decide +kernel
  · dsimp only [trace]; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
private theorem parity20_20367185 :
    (Nat.digits 2 ((2^20367185).descFactorial 20 / 9280784638125)).count 1 % 2 = 0 := by
  let trace : List ℕ := [0, 0, 0, 0, 0, 0, 3806642589780, 18108849008760, 5335913591191, 944456393820, 3899482136612, 2186101867635, 17550286949145, 10390507997055, 12531461849864, 17698374204825, 8621763890639, 16076988000567, 6644668956837, 17234868965907, 706869947277, 17171543925446, 1674007637125, 9715947303627, 13788593569767, 8075362811756, 4642602974846, 6258321476787, 12059235089933, 2708456617022, 8973937080633, 6883449809642, 15394598001302, 8414159524112, 5705313430867, 3506286212619, 15451935365889, 14879945953209, 9362436040329, 4486721056748, 16396820373977, 15685719606334, 1913492489375, 3824595810514, 254681745005, 16579429199344, 11226732984401, 6216559313302, 9461831808832, 2532365456062, 3269238149243, 13056534323873, 12603782099714, 7864189374625, 2396394415765, 15974851037755, 11523959777095, 7595747185285, 7836406058180, 17944961037563, 16218061916992, 3535600229123, 14202046934452, 8820032427233, 13427592842534, 8895108260322, 5210589997182, 12930967600692, 11335411405603, 10726419796662, 5598882113966, 7233525785668, 6681598202188, 16601278656509, 17074466059378, 37414789048, 10848600270326, 7641251025716, 3165448569237, 2690071911806, 12352811907926, 14531702919597, 2146741863174, 7550513396586, 17680114770877, 2806312355766, 12933333714007, 14253809130847, 14017371154903, 4696782941771, 2634525258100, 8865288768131, 11635203202360, 17802081761291, 7268593111253, 16110115388154, 3671485436215, 3573882960175, 14619223979784, 4240340371045, 4938805709028, 17539937192879, 802518166078, 18219305548529, 10881568052728, 7591876978679, 7178706434158, 4344738596101, 1303487101350, 7351246315351, 6422923864351, 4269785732101, 17892972430201, 11136941565749, 11136941565749, 11136941565749, 11136941565749, 11136941565749, 3712313855248, 0, 0, 0, 0, 0, 0, 0]
  rw [show 20367185 = 20367125+60 by decide]
  apply certify20 20367125 trace
  · dsimp only [trace]; decide +kernel
  · dsimp only [trace]; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
private theorem parity20_21387785 :
    (Nat.digits 2 ((2^21387785).descFactorial 20 / 9280784638125)).count 1 % 2 = 0 := by
  let trace : List ℕ := [0, 0, 0, 0, 0, 0, 0, 3806642589780, 18108849008760, 5335913591191, 944456393820, 12126566547150, 1424606233112, 18272795240384, 15075411045645, 7915632093555, 10056585946365, 15223498301324, 12250938380684, 4909450035388, 12364674145316, 2932355101587, 13522555110656, 15556125368276, 13459230070197, 12498332170917, 15285825106374, 4766195496627, 8838841762767, 3125611004756, 18254420444096, 1308569669787, 9327887587077, 7109483282932, 16320274086272, 4024185273633, 1933698002643, 10444846194302, 3464407717112, 10151834518322, 9417627286117, 7218600067869, 602679944889, 30690532208, 13074749895578, 8199034911999, 18066595133469, 13921944470477, 13210843702834, 18000185862124, 1349719907015, 16341375117754, 14104553295845, 18331411426534, 17413922743151, 12403749072053, 15649021567583, 8719555214813, 9456427907992, 682154806373, 17050858152953, 16316095954964, 11576503229874, 6108708271015, 1125595616755, 15236273632345, 11308061040534, 2916909165324, 1649216299430, 11757771278812, 10030872158242, 15909979746623, 8014857175702, 2632842668482, 15845882849212, 10952716939035, 6420232356823, 2735714093683, 10456091697193, 8860535502102, 8251543893163, 3706456735122, 1886568258716, 3521211930419, 2969284346938, 12888964801258, 13362152204128, 14886670210048, 17143372332269, 5898848463326, 2691499218717, 16777266038486, 16301889381057, 7403060100926, 9581951112597, 8915965800566, 13283683428925, 125885686087, 10255487060377, 13943253921516, 5508706003507, 6829181420347, 6340390787287, 10305057299652, 984469086520, 17483780679101, 5152974912881, 7922889347110, 14089767906041, 5773648051421, 3556279256002, 12397801532905, 18520740857215, 18423138381174, 10906910124535, 528026515794, 1147850472204, 4938805709029, 17539937192878, 802518166079, 18219305548528, 10881568052729, 7591876978678, 6687308603878, 7178706434158, 4344738596101, 1303487101350, 7351246315351, 6422923864351, 4269785732101, 14758111758600, 17892972430201, 11136941565749, 11136941565749, 11136941565749, 11136941565749, 11136941565749, 11136941565749, 3712313855248, 0, 0, 0, 0, 0, 0, 0, 0]
  rw [show 21387785 = 21387725+60 by decide]
  apply certify20 21387725 trace
  · dsimp only [trace]; decide +kernel
  · dsimp only [trace]; decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
private theorem parity20_27511385 :
    (Nat.digits 2 ((2^27511385).descFactorial 20 / 9280784638125)).count 1 % 2 = 0 := by
  let trace : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 3806642589780, 18108849008760, 5335913591191, 944456393820, 12126566547150, 4646427556680, 5136920088362, 3423539819384, 226155624645, 11627945948805, 13768899801615, 374242880324, 15963252235934, 10925798279444, 1197136180138, 8652360290067, 17781610522586, 9810241255407, 11843811513026, 9746916214946, 8786018315667, 11870991575937, 4148883540624, 12190823207127, 16263469473267, 10550238715256, 7117478878347, 8733197380286, 16752515297576, 14281766537967, 14534110993432, 5183332520522, 11448812984133, 9358325713142, 17869473904802, 10889035427612, 17576462228823, 17535127818182, 13129941141367, 10930913923119, 4314993800139, 3743004387458, 16787063750828, 11911348767249, 3217339712468, 16529528905988, 17634258325726, 16923157558085, 3150930441124, 5062033762265, 1492119696755, 17816867151095, 3482156005534, 14603598010325, 17413922743151, 12403749072053, 15649021567583, 8719555214813, 9456427907992, 682154806373, 17050858152953, 3623900538233, 1466840533965, 15288817085125, 9821022126265, 4837909472004, 387018211345, 15020374895785, 6629223020575, 10245249737214, 1649216299431, 11757771278813, 10030872158243, 15909979746622, 8014857175703, 2632842668483, 15845882849213, 16457033835893, 14665030794285, 10132546212072, 6448027948933, 14168405552442, 12572849357352, 11963857748412, 7418770590373, 12305744399233, 16735823679716, 18370467351418, 17818539767938, 9176650946009, 9649838348878, 11174356354798, 13431058477019, 1725265921289, 13323476173827, 10116126929217, 5640324472736, 5164947815307, 14827687811426, 17006578823097, 16340593511066, 14848738273587, 5859055718425, 11262827251837, 2830859349877, 6518626211016, 16645647569256, 17966122986097, 17477332353036, 13533367536576, 6592743444403, 15833724507520, 13771466823851, 1440661057631, 4210575491860, 10377454050791, 2061334196171, 30211171001, 18405534677002, 8685487677654, 14808427001964, 14710824525925, 7194596269285, 15377281936795, 15997105893205, 7259679472014, 4938805709029, 17539937192878, 802518166079, 18219305548528, 10881568052729, 7591876978678, 6687308603878, 5146836809579, 7178706434158, 4344738596101, 1303487101350, 7351246315351, 6422923864351, 4269785732101, 14758111758600, 17471054093850, 17892972430201, 11136941565749, 11136941565749, 11136941565749, 11136941565749, 11136941565749, 11136941565749, 11136941565749, 3712313855248, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  rw [show 27511385 = 27511325+60 by decide]
  apply certify20 27511325 trace
  · dsimp only [trace]; decide +kernel
  · dsimp only [trace]; decide +kernel

set_option maxHeartbeats 8000000 in
theorem col20 (a : ℕ) (ha : 60 ≤ a)
    (hr : a % 30618000 ∈ ([1996385, 9140585, 15264185, 20367185, 21387785, 27511385] : List ℕ)) :
    OeisA249609.isEvil ((2^a).choose 20) = true := by
  let ds : List (Bool × ℕ) := [(false, 0), (true, 1031276404198014976), (false, 431565146817638399), (true, 484311774265693696), (false, 610116075740491775), (true, 781536717261618976), (false, 161429736530118959), (true, 1100660601244334256), (false, 12953636989943895), (true, 1150417645851379426), (false, 381922055502194), (true, 1152875223959095066), (false, 4465226757380), (true, 1152921162354335076), (false, 20692933629), (true, 1152921503632905076), (false, 34916945), (true, 1152921504605926426), (false, 16814), (true, 1152921504606846786), (false, 0)]
  refine (periodic_column (k := 20) (t := 60) (l := 15309000) (d := 9280784638125) (z := 18)
    (ds := ds) ha (by decide) modular_order20 ?_ ?_ (by decide)).2 ?_
  · dsimp only [ds]; decide
  · intro w
    rw [pow_add 2 w 60]
    exact falling20 (2^w) (2^60) (by positivity) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h | h | h
  · rw [show (a-60) % (15309000+15309000) + 60 = 1996385 by omega]
    exact parity20_1996385
  · rw [show (a-60) % (15309000+15309000) + 60 = 9140585 by omega]
    exact parity20_9140585
  · rw [show (a-60) % (15309000+15309000) + 60 = 15264185 by omega]
    exact parity20_15264185
  · rw [show (a-60) % (15309000+15309000) + 60 = 20367185 by omega]
    exact parity20_20367185
  · rw [show (a-60) % (15309000+15309000) + 60 = 21387785 by omega]
    exact parity20_21387785
  · rw [show (a-60) % (15309000+15309000) + 60 = 27511385 by omega]
    exact parity20_27511385

end A249609ColumnCertificates

namespace OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H2_R1_H3_R1

open OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1

private theorem cover (t : Fin 90) :
    (340200*t.val+295385)%6123600 ∈ ([1656185, 2336585, 3357185, 3697385, 4037585, 4377785, 5058185, 5738585, 6078785] : List ℕ) ∨
    (340200*t.val+295385)%6123600 ∈ ([295385, 635585, 975785, 1315985, 2676785, 4717985, 5398385] : List ℕ) ∨
    (340200*t.val+295385)%30618000 ∈ ([1996385, 9140585, 15264185, 20367185, 21387785, 27511385] : List ℕ) ∨
    t.val ∈ ([23, 41, 77] : List ℕ) ∨
    t.val = 8 := by
  revert t
  decide +kernel

/-- Residual classes with `t` congruent to `5` modulo 18. -/
def H1 : Prop :=
  ∀ t : ℕ, t % 90 ∈ ([23, 41, 77] : List ℕ) →
    ∃ k ∈ List.range' 1 (2 ^ (340200 * t + 295385)),
      OeisA249609.isEvil ((2 ^ (340200 * t + 295385)).choose k) = true

/-- Residual classes with `t` congruent to `8` modulo 18. -/
def H2 : Prop :=
  ∀ t : ℕ, t % 90 ∈ ([8] : List ℕ) →
    ∃ k ∈ List.range' 1 (2 ^ (340200 * t + 295385)),
      OeisA249609.isEvil ((2 ^ (340200 * t + 295385)).choose k) = true

theorem main : H1 → H2 → OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H2_R1.H3 := by
  intro h1 h2 q hq
  have hq' : q % 105 = 91 := by simpa using hq
  let t := q / 105
  have he : 3240 * q + 545 = 340200 * t + 295385 := by dsimp [t]; omega
  rw [he]
  have reduceMod (d : ℕ) (hd : d ∣ 30618000) :
      (340200 * (t % 90) + 295385) % d = (340200 * t + 295385) % d :=
    (((Nat.mod_modEq t 90).mul_left' 340200).of_dvd hd).add_right 295385
  have cases := cover ⟨t % 90, Nat.mod_lt _ (by decide)⟩
  dsimp only at cases
  rw [reduceMod 6123600 (by decide), reduceMod 30618000 (by decide)] at cases
  have hbig : 32 ≤ 2 ^ (340200 * t + 295385) :=
    le_trans (by decide : 32 ≤ 2^5) (Nat.pow_le_pow_right (by decide) (by omega))
  rcases cases with h | h | h | h | h
  · exact witness _ 18 (by decide) (by omega) (A249609ColumnCertificates.col18 _ (by omega) h)
  · exact witness _ 19 (by decide) (by omega) (A249609ColumnCertificates.col19 _ (by omega) h)
  · exact witness _ 20 (by decide) (by omega) (A249609ColumnCertificates.col20 _ (by omega) h)
  · exact h1 t h
  · exact h2 t (by simp [h])

end OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H2_R1_H3_R1
