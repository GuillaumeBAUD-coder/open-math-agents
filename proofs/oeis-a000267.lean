import OMAStatements.S_oeis_a000267

namespace BinaryPartitionLength

/-- The largest weight for a fixed binary length comes from a balanced rectangle. -/
private theorem balanced_rectangle (n : ℕ) :
    let l := Nat.sqrt (4 * n + 1)
    ∃ r m : ℕ, 0 < r ∧ 0 < m ∧ r + m = l + 1 ∧ l ≤ n + 1 ∧ n + 1 ≤ r * m := by
  dsimp
  let l := Nat.sqrt (4 * n + 1)
  have hl : 0 < l := by
    change 1 ≤ Nat.sqrt (4 * n + 1)
    exact Nat.le_sqrt'.mpr (by omega)
  have hlarge : 4 * n + 1 < (l + 1) ^ 2 := Nat.lt_succ_sqrt' _
  have hlt : l < n + 2 := by
    apply Nat.sqrt_lt'.mpr
    nlinarith
  let r := (l + 1) / 2
  have hp : 2 * r ≤ l + 1 ∧ l + 1 ≤ 2 * r + 1 := by dsimp [r]; omega
  by_cases he : l + 1 = 2 * r
  · refine ⟨r, r, by omega, by omega, by omega, by omega, ?_⟩
    rw [he] at hlarge
    nlinarith only [hlarge]
  · have he' : l + 1 = 2 * r + 1 := by omega
    refine ⟨r, r + 1, by omega, by omega, by omega, by omega, ?_⟩
    rw [he'] at hlarge
    have h : 4 * n < 4 * (r * (r + 1)) := by nlinarith only [hlarge]
    omega

/-- A shorter code cannot reach weight `n + 1`, even with all parts maximal. -/
private theorem shorter_rectangle (n r m : ℕ) (h : r + m ≤ Nat.sqrt (4 * n + 1)) :
    r * m ≤ n := by
  have hquad : (r + m) ^ 2 ≤ 4 * n + 1 := Nat.le_sqrt'.mp h
  have hprod : 4 * (r * m) ≤ 4 * n + 1 := by
    nlinarith only [hquad, sq_nonneg ((r : ℤ) - m)]
  omega

private theorem bounded_parts (r m w : ℕ) (hm : 0 < m) (hlo : r ≤ w) (hhi : w ≤ r * m) :
    ∃ t : List ℕ, t.length = r ∧ t.sum = w ∧ ∀ k ∈ t, 0 < k ∧ k ≤ m := by
  induction r generalizing w with
  | zero =>
    have hw : w = 0 := by simpa using hhi
    subst w
    exact ⟨[], by simp⟩
  | succ r ih =>
    let first := min m (w - r)
    have hfirst : 0 < first ∧ first ≤ m := by dsimp [first]; omega
    have hlow : r ≤ w - first := by dsimp [first]; omega
    have hhigh : w - first ≤ r * m := by
      have hu : w ≤ r * m + m := by simpa [Nat.succ_mul] using hhi
      have hrm : r ≤ r * m := by simpa using Nat.mul_le_mul_left r hm
      dsimp [first]
      rw [min_def]
      split <;> omega
    obtain ⟨t, ht, hs, hall⟩ := ih (w - first) hlow hhigh
    refine ⟨first :: t, by simp [ht], ?_, ?_⟩
    · simp only [List.sum_cons, hs]
      dsimp [first]
      omega
    · intro k hk
      rcases List.mem_cons.mp hk with rfl | hk
      · exact hfirst
      · exact hall k hk

private def decodeRuns : List ℕ → List ℕ
  | [] => []
  | first :: rs => rs.scanl (fun part run => part + (run - 1)) first

private theorem decodeRuns_length (rs : List ℕ) : (decodeRuns rs).length = rs.length := by
  cases rs <;> simp [decodeRuns, List.length_scanl]

private theorem sum_of_positive_runs (rs : List ℕ) (h : ∀ x ∈ rs, 0 < x) :
    (rs.map (fun x => x - 1)).sum + rs.length = rs.sum := by
  induction rs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have hs := ih (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons, List.length_cons, List.sum_cons]
    omega

private theorem scan_parts_bound (rs : List ℕ) (start x : ℕ)
    (hx : x ∈ rs.scanl (fun part run => part + (run - 1)) start) :
    x ≤ start + (rs.map (fun y => y - 1)).sum := by
  induction rs generalizing start with
  | nil => simpa using le_of_eq (by simpa using hx : x = start)
  | cons a as ih =>
    rw [List.scanl_cons, List.mem_cons] at hx
    simp only [List.map_cons, List.sum_cons]
    rcases hx with rfl | hx
    · omega
    · have := ih (start + (a - 1)) hx
      omega

private theorem sum_le_length_mul {parts : List ℕ} {m : ℕ} (h : ∀ x ∈ parts, x ≤ m) :
    parts.sum ≤ parts.length * m := by
  induction parts with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have hsum := ih (fun y hy => h y (by simp [hy]))
    simp only [List.sum_cons, List.length_cons, Nat.succ_mul]
    omega

private theorem decodeRuns_bound {rs : List ℕ} (hne : rs ≠ []) (hp : ∀ a ∈ rs, 0 < a) :
    ∃ m : ℕ, rs.length + m = rs.sum + 1 ∧ (decodeRuns rs).sum ≤ rs.length * m := by
  cases rs with
  | nil => contradiction
  | cons a rs =>
    refine ⟨a + (rs.map (fun y => y - 1)).sum, ?_, ?_⟩
    · have hh := sum_of_positive_runs rs (fun y hy => hp y (by simp [hy]))
      simp only [List.length_cons, List.sum_cons]
      omega
    · rw [← decodeRuns_length (a :: rs)]
      exact sum_le_length_mul (fun x hx => scan_parts_bound rs a x hx)

private theorem bitLength {n : ℕ} (hn : n ≠ 0) : n.bits.length = n.log2 + 1 := by
  rw [Nat.size_eq_bits_len]
  have hu : n.size ≤ n.log2 + 1 := Nat.size_le.mpr ((Nat.log2_lt hn).mp (Nat.lt_succ_self _))
  have hl : n.log2 < n.size := Nat.lt_size.mpr ((Nat.le_log2 hn).mp le_rfl)
  omega

private theorem bits_at (n i : ℕ) (hi : i < n.bits.length) :
    n.bits[i]? = some (n.testBit i) := by
  induction n using Nat.binaryRec' generalizing i with
  | zero => simp at hi
  | bit b n h ih =>
    rw [Nat.bits_append_bit n b h] at hi ⊢
    cases i with
    | zero => exact congrArg some (Nat.bodd_bit b n).symm
    | succ i =>
      rw [List.getElem?_cons_succ, Nat.testBit_bit_succ]
      exact ih i (Nat.lt_of_succ_lt_succ hi)

private theorem bits_eq_range {n : ℕ} (hn : n ≠ 0) :
    (List.range (n.log2 + 1)).map n.testBit = n.bits := by
  apply List.ext_getElem
  · simp [bitLength hn]
  · intro i h₁ h₂
    have he := List.getElem?_eq_some_iff.mp (bits_at n i h₂)
    obtain ⟨h, hv⟩ := he
    simpa only [List.getElem_map, List.getElem_range] using hv.symm

private def codeRuns (n : ℕ) : List ℕ :=
  ((n.bits.splitBy (· == ·)).map List.length)

private theorem codeRuns_sum (n : ℕ) : (codeRuns n).sum = n.bits.length := by
  rw [codeRuns, ← List.length_flatten, List.flatten_splitBy]

private theorem codeRuns_pos (n : ℕ) : ∀ x ∈ codeRuns n, 0 < x := by
  intro x hx
  obtain ⟨chunk, hm, rfl⟩ := List.mem_map.mp hx
  exact List.length_pos_iff.mpr (fun he => List.nil_notMem_splitBy (· == ·) n.bits (he ▸ hm))

private theorem codeRuns_ne_nil {n : ℕ} (hn : n ≠ 0) : codeRuns n ≠ [] := by
  intro hz
  have hsum := codeRuns_sum n
  rw [hz, List.sum_nil, bitLength hn] at hsum
  omega

private theorem decoded_weight {n : ℕ} (hn : n ≠ 0) :
    OMA.S_oeis_a000267.partitionWeight n = (decodeRuns (codeRuns n)).sum := by
  rw [OMA.S_oeis_a000267.partitionWeight, if_neg hn, bits_eq_range hn]
  change (match codeRuns n with
    | [] => 0
    | first :: rest => (rest.scanl (fun part run => part + (run - 1)) first).sum) = _
  cases codeRuns n <;> rfl

private theorem insufficient_length {code n : ℕ} (h : code.log2 + 1 < Nat.sqrt (4 * n + 1)) :
    OMA.S_oeis_a000267.partitionWeight code ≠ n + 1 := by
  by_cases hn : code = 0
  · simp [hn, OMA.S_oeis_a000267.partitionWeight]
  · obtain ⟨m, hm, hb⟩ := decodeRuns_bound (codeRuns_ne_nil hn) (codeRuns_pos code)
    rw [codeRuns_sum, bitLength hn] at hm
    have hbound := shorter_rectangle n (codeRuns code).length m (by omega)
    rw [decoded_weight hn]
    omega

private def followRuns (start : ℕ) : List ℕ → List ℕ
  | [] => []
  | p :: ps => (p - start + 1) :: followRuns p ps

private theorem followRuns_length (start : ℕ) (ps : List ℕ) :
    (followRuns start ps).length = ps.length := by
  induction ps generalizing start with
  | nil => rfl
  | cons p ps ih => simp [followRuns, ih]

private theorem followRuns_pos (start : ℕ) (ps : List ℕ) :
    ∀ x ∈ followRuns start ps, 0 < x := by
  induction ps generalizing start with
  | nil => simp [followRuns]
  | cons p ps ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    · exact ih p x hx

private theorem scan_followRuns (start : ℕ) (ps : List ℕ) (h : (start :: ps).Pairwise (· ≤ ·)) :
    (followRuns start ps).scanl (fun part run => part + (run - 1)) start = start :: ps := by
  induction ps generalizing start with
  | nil => simp [followRuns]
  | cons p ps ih =>
    have hparts := List.pairwise_cons.mp h
    have hle := hparts.1 p (by simp)
    have hstep : start + (p - start + 1 - 1) = p := by omega
    rw [followRuns, List.scanl_cons, hstep, ih p hparts.2]

private theorem followRuns_sum (start m : ℕ) (ps : List ℕ)
    (h : (start :: (ps ++ [m])).Pairwise (· ≤ ·)) :
    (followRuns start (ps ++ [m])).sum + start = m + (ps ++ [m]).length := by
  induction ps generalizing start with
  | nil =>
    have hle := (List.pairwise_cons.mp h).1 m (by simp)
    simp only [List.nil_append, followRuns, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil]
    omega
  | cons p ps ih =>
    have hr := List.pairwise_cons.mp h
    have hs := ih p hr.2
    have hp := hr.1 p (by simp)
    simp only [List.cons_append, followRuns, List.sum_cons, List.length_cons]
    omega

private theorem encode_parts {m : ℕ} (hm : 0 < m) (ps : List ℕ)
    (hp : ∀ a ∈ ps, 0 < a) (hs : (ps ++ [m]).Pairwise (· ≤ ·)) :
    ∃ rs : List ℕ, rs ≠ [] ∧ (∀ a ∈ rs, 0 < a) ∧
      decodeRuns rs = ps ++ [m] ∧ rs.sum + 1 = (ps ++ [m]).length + m := by
  cases ps with
  | nil =>
    refine ⟨[m], by simp, by simpa, ?_, ?_⟩
    · simp [decodeRuns]
    · simp [Nat.add_comm]
  | cons a ps =>
    refine ⟨a :: followRuns a (ps ++ [m]), by simp, ?_, ?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hp x (by simp)
      · exact followRuns_pos _ _ _ hx
    · exact scan_followRuns a (ps ++ [m]) hs
    · have hsum := followRuns_sum a m ps hs
      simp only [List.sum_cons, List.cons_append, List.length_cons]
      omega

/-- Encode each run with the bit determined by the parity of the number of runs after it. -/
private def emitRuns : List ℕ → List (List Bool)
  | [] => []
  | r :: rs => List.replicate r (decide (rs.length % 2 = 0)) :: emitRuns rs

private theorem emitRuns_lengths (rs : List ℕ) : (emitRuns rs).map List.length = rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [emitRuns, ih]

private theorem replicate_nonempty {r : ℕ} (hr : 0 < r) (b : Bool) : List.replicate r b ≠ [] := by
  exact List.length_pos_iff.mp (by simpa using hr)

private theorem emit_no_empty {rs : List ℕ} (hp : ∀ r ∈ rs, 0 < r) :
    [] ∉ emitRuns rs := by
  intro h
  have h0 : 0 ∈ rs := by
    rw [← emitRuns_lengths rs]
    exact List.mem_map.mpr ⟨[], h, rfl⟩
  exact (hp 0 h0).false

private theorem emit_uniform (rs : List ℕ) :
    ∀ a ∈ emitRuns rs, a.IsChain (fun x y => (x == y) = true) := by
  induction rs with
  | nil => simp [emitRuns]
  | cons r rs ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact List.isChain_replicate_of_rel r (by simp)
    · exact ih a ha

private theorem emit_alternating {rs : List ℕ} (hp : ∀ r ∈ rs, 0 < r) :
    (emitRuns rs).IsChain fun a b => ∃ ha hb, (a.getLast ha == b.head hb) = false := by
  induction rs with
  | nil => exact List.isChain_nil
  | cons r rs ih =>
    cases rs with
    | nil => simp [emitRuns]
    | cons q qs =>
      have hr := hp r (by simp)
      have hq := hp q (by simp)
      have hp' (z : ℕ) (hz : z ∈ q :: qs) := hp z (by simp [hz])
      rw [emitRuns, emitRuns, List.isChain_cons_cons]
      refine ⟨?_, ih hp'⟩
      refine ⟨replicate_nonempty hr _, replicate_nonempty hq _, ?_⟩
      rw [List.getLast_replicate, List.head_replicate]
      by_cases hs : qs.length % 2 = 0
      · have he : (qs.length + 1) % 2 ≠ 0 := by omega
        simp [List.length_cons, hs, he]
      · have he : (qs.length + 1) % 2 = 0 := by omega
        simp [List.length_cons, hs, he]

private theorem emit_last {rs : List ℕ} (hne : rs ≠ []) (hp : ∀ r ∈ rs, 0 < r) :
    (emitRuns rs).flatten.getLast? = some true := by
  induction rs with
  | nil => contradiction
  | cons r rs ih =>
    cases rs with
    | nil =>
      have hr : r ≠ 0 := Nat.ne_of_gt (hp r (by simp))
      simp [emitRuns, List.getLast?_replicate, hr]
    | cons q qs =>
      have ih' := ih (by simp) (fun z hz => hp z (by simp [hz]))
      rw [emitRuns, List.flatten_cons, List.getLast?_append, ih']
      rfl

private theorem emit_split {rs : List ℕ} (hp : ∀ r ∈ rs, 0 < r) :
    (emitRuns rs).flatten.splitBy (· == ·) = emitRuns rs :=
  List.splitBy_flatten (emit_no_empty hp) (emit_uniform rs) (emit_alternating hp)

private theorem code_of_bits {bs : List Bool} (hlast : bs.getLast? = some true) :
    ∃ code : ℕ, code ≠ 0 ∧ code.bits = bs := by
  obtain ⟨cs, rfl⟩ := List.getLast?_eq_some_iff.mp hlast
  let ds := (cs ++ [true]).map Bool.toNat
  let code := Nat.ofDigits 2 ds
  have hd : ds = cs.map Bool.toNat ++ [1] := by simp [ds]
  have hb : Nat.digits 2 code = ds := by
    apply Nat.digits_ofDigits 2 (by decide)
    · intro v hv
      obtain ⟨b, _, rfl⟩ := List.mem_map.mp hv
      cases b <;> decide
    · intro hn
      simp [hd]
  have hc : code ≠ 0 := by
    intro he
    rw [he, Nat.digits_zero, hd] at hb
    simp at hb
  refine ⟨code, hc, ?_⟩
  have hfn : (fun b : Bool => cond b (1 : ℕ) 0) = Bool.toNat := by funext b; cases b <;> rfl
  rw [Nat.digits_two_eq_bits, hfn] at hb
  have hinj : Function.Injective Bool.toNat := by
    intro a b hab
    cases a <;> cases b <;> simp_all
  exact (List.map_injective_iff.mpr hinj) hb

private theorem code_of_runs {rs : List ℕ} (hne : rs ≠ []) (hp : ∀ x ∈ rs, 0 < x) :
    ∃ code : ℕ, code.log2 + 1 = rs.sum ∧
      OMA.S_oeis_a000267.partitionWeight code = (decodeRuns rs).sum := by
  obtain ⟨code, hcode, hbits⟩ := code_of_bits (emit_last hne hp)
  have hrun : codeRuns code = rs := by
    rw [codeRuns, hbits, emit_split hp, emitRuns_lengths]
  exact ⟨code, (bitLength hcode).symm.trans (by rw [← codeRuns_sum, hrun]),
    by rw [decoded_weight hcode, hrun]⟩

private theorem achievable_weight (n : ℕ) :
    ∃ code : ℕ, code.log2 + 1 = Nat.sqrt (4 * n + 1) ∧
      OMA.S_oeis_a000267.partitionWeight code = n + 1 := by
  obtain ⟨r, m, hr, hm, hdim, hl, hfit⟩ := balanced_rectangle n
  have hsub : r - 1 ≤ n + 1 - m := by omega
  have hexact : (r - 1) * m + m = r * m := by
    rw [← Nat.succ_mul, show (r - 1).succ = r by omega]
  have hsup : n + 1 - m ≤ (r - 1) * m := by omega
  obtain ⟨ps, hlen, hsum, hbound⟩ := bounded_parts (r - 1) m (n + 1 - m) hm hsub hsup
  let sorted := ps.mergeSort (· ≤ ·)
  have hperm : sorted.Perm ps := List.mergeSort_perm _ _
  have hsorted : sorted.Pairwise (· ≤ ·) := List.sortedLE_mergeSort.pairwise
  have hps (x : ℕ) (hx : x ∈ sorted) : 0 < x ∧ x ≤ m :=
    hbound x (hperm.mem_iff.mp hx)
  have hfull : (sorted ++ [m]).Pairwise (· ≤ ·) := by
    refine List.pairwise_append.mpr ⟨hsorted, by simp, ?_⟩
    intro x hx y hy
    have hy' : y = m := by simpa using hy
    subst y
    exact (hps x hx).2
  obtain ⟨rs, hne, hpos, hdecode, hsize⟩ := encode_parts hm sorted (fun x hx => (hps x hx).1) hfull
  obtain ⟨code, hcLen, hcWeight⟩ := code_of_runs hne hpos
  have hsl : sorted.length = r - 1 := hperm.length_eq.trans hlen
  have hss : sorted.sum = n + 1 - m := hperm.sum_eq.trans hsum
  rw [List.length_append, List.length_singleton, hsl] at hsize
  rw [hdecode, List.sum_append, List.sum_singleton, hss] at hcWeight
  exact ⟨code, by omega, by omega⟩

theorem minimum_code (n : ℕ) :
    ∃ code : ℕ, OMA.S_oeis_a000267.partitionWeight code = n + 1 ∧
      (∀ k < code, OMA.S_oeis_a000267.partitionWeight k ≠ n + 1) ∧
      code.log2 + 1 = Nat.sqrt (4 * n + 1) := by
  obtain ⟨q, hqLen, hqWeight⟩ := achievable_weight n
  have hex : ∃ k, OMA.S_oeis_a000267.partitionWeight k = n + 1 := ⟨q, hqWeight⟩
  classical
  let k := Nat.find hex
  have hk : OMA.S_oeis_a000267.partitionWeight k = n + 1 := Nat.find_spec hex
  have hk0 : k ≠ 0 := by
    intro h
    simp [h, OMA.S_oeis_a000267.partitionWeight] at hk
  have hq0 : q ≠ 0 := by
    rintro rfl
    simp [OMA.S_oeis_a000267.partitionWeight] at hqWeight
  have hkle : k ≤ q := Nat.find_min' hex hqWeight
  have hmono : k.log2 ≤ q.log2 := (Nat.le_log2 hq0).mpr
    (((Nat.le_log2 hk0).mp le_rfl).trans hkle)
  refine ⟨k, hk, fun i hi => Nat.find_min hex hi, ?_⟩
  have hlong : ¬ k.log2 + 1 < Nat.sqrt (4 * n + 1) := fun h => insufficient_length h hk
  omega

end BinaryPartitionLength

theorem OMA.solution : type_of% @OMA.S_oeis_a000267.main :=
  BinaryPartitionLength.minimum_code
