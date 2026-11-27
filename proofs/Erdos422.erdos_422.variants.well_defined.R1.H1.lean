import OMAReductions.R_Erdos422_erdos_422_variants_well_defined_R1

-- Step Erdos422.erdos_422.variants.well_defined.R1.H1
-- Credit: @caa1982

private def q : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | n + 3 =>
    let a := q (n + 2)
    let b := q (n + 1)
    if _h : 0 < a ∧ a < n + 3 ∧ 0 < b ∧ b < n + 3 then
      q (n + 3 - a) + q (n + 3 - b)
    else 0

private lemma q_rec (n : ℕ) (hn : 2 < n) :
    q n = if 0 < q (n - 1) ∧ q (n - 1) < n ∧ 0 < q (n - 2) ∧ q (n - 2) < n then
      q (n - q (n - 1)) + q (n - q (n - 2)) else 0 := by
  rcases n with _ | _ | _ | m
  · omega
  · omega
  · omega
  · rw [q]
    simp only [Nat.add_sub_cancel, show m + 1 + 1 + 1 - 2 = m + 1 by omega, dite_eq_ite]

private inductive T
  | leaf (v : ℕ)
  | node (l r : T)

private def T.get : T → ℕ → ℕ → ℕ
  | T.leaf v, _, _ => v
  | T.node l r, 0, _ => l.get 0 0
  | T.node l r, d + 1, i =>
    if i < 2 ^ d then l.get d i else r.get d (i - 2 ^ d)

private def qTree : T := T.node (T.node (T.node (T.node (T.node (T.node (T.node (T.node (T.node (T.node (T.leaf 0) (T.leaf 1)) (T.node (T.leaf 1) (T.leaf 2))) (T.node (T.node (T.leaf 3) (T.leaf 3)) (T.node (T.leaf 4) (T.leaf 5)))) (T.node (T.node (T.node (T.leaf 5) (T.leaf 6)) (T.node (T.leaf 6) (T.leaf 6))) (T.node (T.node (T.leaf 8) (T.leaf 8)) (T.node (T.leaf 8) (T.leaf 10))))) (T.node (T.node (T.node (T.node (T.leaf 9) (T.leaf 10)) (T.node (T.leaf 11) (T.leaf 11))) (T.node (T.node (T.leaf 12) (T.leaf 12)) (T.node (T.leaf 12) (T.leaf 12)))) (T.node (T.node (T.node (T.leaf 16) (T.leaf 14)) (T.node (T.leaf 14) (T.leaf 16))) (T.node (T.node (T.leaf 16) (T.leaf 16)) (T.node (T.leaf 16) (T.leaf 20)))))) (T.node (T.node (T.node (T.node (T.node (T.leaf 17) (T.leaf 17)) (T.node (T.leaf 20) (T.leaf 21))) (T.node (T.node (T.leaf 19) (T.leaf 20)) (T.node (T.leaf 22) (T.leaf 21)))) (T.node (T.node (T.node (T.leaf 22) (T.leaf 23)) (T.node (T.leaf 23) (T.leaf 24))) (T.node (T.node (T.leaf 24) (T.leaf 24)) (T.node (T.leaf 24) (T.leaf 24))))) (T.node (T.node (T.node (T.node (T.leaf 32) (T.leaf 24)) (T.node (T.leaf 25) (T.leaf 30))) (T.node (T.node (T.leaf 28) (T.leaf 26)) (T.node (T.leaf 30) (T.leaf 30)))) (T.node (T.node (T.node (T.leaf 28) (T.leaf 32)) (T.node (T.leaf 30) (T.leaf 32))) (T.node (T.node (T.leaf 32) (T.leaf 32)) (T.node (T.leaf 32) (T.leaf 40))))))) (T.node (T.node (T.node (T.node (T.node (T.node (T.leaf 33) (T.leaf 31)) (T.node (T.leaf 38) (T.leaf 35))) (T.node (T.node (T.leaf 33) (T.leaf 39)) (T.node (T.leaf 40) (T.leaf 37)))) (T.node (T.node (T.node (T.leaf 38) (T.leaf 40)) (T.node (T.leaf 39) (T.leaf 40))) (T.node (T.node (T.leaf 39) (T.leaf 42)) (T.node (T.leaf 40) (T.leaf 41))))) (T.node (T.node (T.node (T.node (T.leaf 43) (T.leaf 44)) (T.node (T.leaf 43) (T.leaf 43))) (T.node (T.node (T.leaf 46) (T.leaf 44)) (T.node (T.leaf 45) (T.leaf 47)))) (T.node (T.node (T.node (T.leaf 47) (T.leaf 46)) (T.node (T.leaf 48) (T.leaf 48))) (T.node (T.node (T.leaf 48) (T.leaf 48)) (T.node (T.leaf 48) (T.leaf 48)))))) (T.node (T.node (T.node (T.node (T.node (T.leaf 64) (T.leaf 41)) (T.node (T.leaf 52) (T.leaf 54))) (T.node (T.node (T.leaf 56) (T.leaf 48)) (T.node (T.leaf 54) (T.leaf 54)))) (T.node (T.node (T.node (T.leaf 50) (T.leaf 60)) (T.node (T.leaf 52) (T.leaf 54))) (T.node (T.node (T.leaf 58) (T.leaf 60)) (T.node (T.leaf 53) (T.leaf 60))))) (T.node (T.node (T.node (T.node (T.leaf 60) (T.leaf 52)) (T.node (T.leaf 62) (T.leaf 66))) (T.node (T.node (T.leaf 55) (T.leaf 62)) (T.node (T.leaf 68) (T.leaf 62)))) (T.node (T.node (T.node (T.leaf 58) (T.leaf 72)) (T.node (T.leaf 58) (T.leaf 61))) (T.node (T.node (T.leaf 78) (T.leaf 57)) (T.node (T.leaf 71) (T.leaf 68)))))))) (T.node (T.node (T.node (T.node (T.node (T.node (T.node (T.leaf 64) (T.leaf 63)) (T.node (T.leaf 73) (T.leaf 63))) (T.node (T.node (T.leaf 71) (T.leaf 72)) (T.node (T.leaf 72) (T.leaf 80)))) (T.node (T.node (T.node (T.leaf 61) (T.leaf 71)) (T.node (T.leaf 77) (T.leaf 65))) (T.node (T.node (T.leaf 80) (T.leaf 71)) (T.node (T.leaf 69) (T.leaf 77))))) (T.node (T.node (T.node (T.node (T.leaf 75) (T.leaf 73)) (T.node (T.leaf 77) (T.leaf 79))) (T.node (T.node (T.leaf 76) (T.leaf 80)) (T.node (T.leaf 79) (T.leaf 75)))) (T.node (T.node (T.node (T.leaf 82) (T.leaf 77)) (T.node (T.leaf 80) (T.leaf 80))) (T.node (T.node (T.leaf 78) (T.leaf 83)) (T.node (T.leaf 83) (T.leaf 78)))))) (T.node (T.node (T.node (T.node (T.node (T.leaf 85) (T.leaf 82)) (T.node (T.leaf 85) (T.leaf 84))) (T.node (T.node (T.leaf 84) (T.leaf 88)) (T.node (T.leaf 83) (T.leaf 87)))) (T.node (T.node (T.node (T.leaf 88) (T.leaf 87)) (T.node (T.leaf 86) (T.leaf 90))) (T.node (T.node (T.leaf 88) (T.leaf 87)) (T.node (T.leaf 92) (T.leaf 90))))) (T.node (T.node (T.node (T.node (T.leaf 91) (T.leaf 92)) (T.node (T.leaf 92) (T.leaf 94))) (T.node (T.node (T.leaf 92) (T.leaf 93)) (T.node (T.leaf 94) (T.leaf 94)))) (T.node (T.node (T.node (T.leaf 96) (T.leaf 94)) (T.node (T.leaf 96) (T.leaf 96))) (T.node (T.node (T.leaf 96) (T.leaf 96)) (T.node (T.leaf 96) (T.leaf 96))))))) (T.node (T.node (T.node (T.node (T.node (T.node (T.leaf 128) (T.leaf 72)) (T.node (T.leaf 96) (T.leaf 115))) (T.node (T.node (T.leaf 100) (T.leaf 84)) (T.node (T.leaf 114) (T.leaf 110)))) (T.node (T.node (T.node (T.leaf 93) (T.leaf 106)) (T.node (T.leaf 124) (T.leaf 82))) (T.node (T.node (T.leaf 101) (T.leaf 111)) (T.node (T.leaf 108) (T.leaf 118))))) (T.node (T.node (T.node (T.node (T.leaf 104) (T.leaf 108)) (T.node (T.leaf 106) (T.leaf 114))) (T.node (T.node (T.leaf 104) (T.leaf 114)) (T.node (T.leaf 109) (T.leaf 100)))) (T.node (T.node (T.node (T.leaf 109) (T.leaf 120)) (T.node (T.leaf 112) (T.leaf 108))) (T.node (T.node (T.leaf 118) (T.leaf 106)) (T.node (T.leaf 105) (T.leaf 130)))))) (T.node (T.node (T.node (T.node (T.node (T.leaf 110) (T.leaf 114)) (T.node (T.leaf 115) (T.leaf 112))) (T.node (T.node (T.leaf 107) (T.leaf 120)) (T.node (T.leaf 114) (T.leaf 122)))) (T.node (T.node (T.node (T.leaf 121) (T.leaf 120)) (T.node (T.leaf 114) (T.leaf 138))) (T.node (T.node (T.leaf 110) (T.leaf 122)) (T.node (T.leaf 119) (T.leaf 120))))) (T.node (T.node (T.node (T.node (T.leaf 130) (T.leaf 132)) (T.node (T.leaf 113) (T.leaf 133))) (T.node (T.node (T.leaf 123) (T.leaf 118)) (T.node (T.leaf 125) (T.leaf 121)))) (T.node (T.node (T.node (T.leaf 129) (T.leaf 122)) (T.node (T.leaf 136) (T.leaf 129))) (T.node (T.node (T.leaf 116) (T.leaf 149)) (T.node (T.leaf 137) (T.leaf 120))))))))) (T.node (T.node (T.node (T.node (T.node (T.node (T.node (T.node (T.leaf 123) (T.leaf 143)) (T.node (T.leaf 146) (T.leaf 107))) (T.node (T.node (T.leaf 139) (T.leaf 138)) (T.node (T.leaf 139) (T.leaf 135)))) (T.node (T.node (T.node (T.leaf 120) (T.leaf 146)) (T.node (T.leaf 135) (T.leaf 143))) (T.node (T.node (T.leaf 129) (T.leaf 151)) (T.node (T.leaf 133) (T.leaf 135))))) (T.node (T.node (T.node (T.node (T.leaf 136) (T.leaf 148)) (T.node (T.leaf 148) (T.leaf 136))) (T.node (T.node (T.leaf 144) (T.leaf 143)) (T.node (T.leaf 152) (T.leaf 129)))) (T.node (T.node (T.node (T.leaf 139) (T.leaf 151)) (T.node (T.leaf 140) (T.leaf 148))) (T.node (T.node (T.leaf 136) (T.leaf 151)) (T.node (T.leaf 159) (T.leaf 125)))))) (T.node (T.node (T.node (T.node (T.node (T.leaf 147) (T.leaf 153)) (T.node (T.leaf 148) (T.leaf 154))) (T.node (T.node (T.leaf 152) (T.leaf 136)) (T.node (T.leaf 152) (T.leaf 155)))) (T.node (T.node (T.node (T.leaf 146) (T.leaf 144)) (T.node (T.leaf 162) (T.leaf 151))) (T.node (T.node (T.leaf 157) (T.leaf 154)) (T.node (T.leaf 149) (T.leaf 160))))) (T.node (T.node (T.node (T.node (T.leaf 155) (T.leaf 152)) (T.node (T.leaf 155) (T.leaf 162))) (T.node (T.node (T.leaf 154) (T.leaf 159)) (T.node (T.leaf 153) (T.leaf 165)))) (T.node (T.node (T.node (T.leaf 157) (T.leaf 154)) (T.node (T.leaf 168) (T.leaf 161))) (T.node (T.node (T.leaf 156) (T.leaf 160)) (T.node (T.leaf 168) (T.leaf 153))))))) (T.node (T.node (T.node (T.node (T.node (T.node (T.leaf 169) (T.leaf 170)) (T.node (T.leaf 159) (T.leaf 161))) (T.node (T.node (T.leaf 172) (T.leaf 161)) (T.node (T.leaf 168) (T.leaf 161)))) (T.node (T.node (T.node (T.leaf 172) (T.leaf 171)) (T.node (T.leaf 161) (T.leaf 171))) (T.node (T.node (T.leaf 172) (T.leaf 167)) (T.node (T.leaf 172) (T.leaf 172))))) (T.node (T.node (T.node (T.node (T.leaf 168) (T.leaf 175)) (T.node (T.leaf 170) (T.leaf 171))) (T.node (T.node (T.leaf 173) (T.leaf 174)) (T.node (T.leaf 175) (T.leaf 175)))) (T.node (T.node (T.node (T.leaf 174) (T.leaf 176)) (T.node (T.leaf 174) (T.leaf 177))) (T.node (T.node (T.leaf 182) (T.leaf 175)) (T.node (T.leaf 178) (T.leaf 178)))))) (T.node (T.node (T.node (T.node (T.node (T.leaf 184) (T.leaf 177)) (T.node (T.leaf 178) (T.leaf 184))) (T.node (T.node (T.leaf 180) (T.leaf 179)) (T.node (T.leaf 186) (T.leaf 179)))) (T.node (T.node (T.node (T.leaf 185) (T.leaf 185)) (T.node (T.leaf 184) (T.leaf 186))) (T.node (T.node (T.leaf 184) (T.leaf 187)) (T.node (T.leaf 188) (T.leaf 186))))) (T.node (T.node (T.node (T.node (T.leaf 186) (T.leaf 188)) (T.node (T.leaf 190) (T.leaf 187))) (T.node (T.node (T.leaf 188) (T.leaf 190)) (T.node (T.leaf 192) (T.leaf 188)))) (T.node (T.node (T.node (T.leaf 192) (T.leaf 190)) (T.node (T.leaf 192) (T.leaf 192))) (T.node (T.node (T.leaf 192) (T.leaf 192)) (T.node (T.leaf 192) (T.leaf 192)))))))) (T.node (T.node (T.node (T.node (T.node (T.node (T.node (T.leaf 256) (T.leaf 135)) (T.node (T.leaf 202) (T.leaf 210))) (T.node (T.node (T.leaf 188) (T.leaf 200)) (T.node (T.leaf 220) (T.leaf 186)))) (T.node (T.node (T.node (T.leaf 196) (T.leaf 202)) (T.node (T.leaf 242) (T.leaf 149))) (T.node (T.node (T.leaf 201) (T.leaf 229)) (T.node (T.leaf 171) (T.leaf 193))))) (T.node (T.node (T.node (T.node (T.leaf 238) (T.leaf 188)) (T.node (T.leaf 193) (T.leaf 206))) (T.node (T.node (T.leaf 228) (T.leaf 202)) (T.node (T.leaf 193) (T.leaf 220)))) (T.node (T.node (T.node (T.leaf 196) (T.leaf 210)) (T.node (T.leaf 202) (T.leaf 214))) (T.node (T.node (T.leaf 220) (T.leaf 182)) (T.node (T.leaf 217) (T.leaf 234)))))) (T.node (T.node (T.node (T.node (T.node (T.leaf 204) (T.leaf 208)) (T.node (T.leaf 215) (T.leaf 215))) (T.node (T.node (T.leaf 222) (T.leaf 218)) (T.node (T.leaf 194) (T.leaf 231)))) (T.node (T.node (T.node (T.leaf 186) (T.leaf 216)) (T.node (T.leaf 236) (T.leaf 210))) (T.node (T.node (T.leaf 240) (T.leaf 204)) (T.node (T.leaf 211) (T.leaf 230))))) (T.node (T.node (T.node (T.node (T.leaf 230) (T.leaf 164)) (T.node (T.leaf 234) (T.leaf 241))) (T.node (T.node (T.leaf 239) (T.leaf 214)) (T.node (T.leaf 220) (T.leaf 222)))) (T.node (T.node (T.node (T.leaf 230) (T.leaf 222)) (T.node (T.leaf 222) (T.leaf 212))) (T.node (T.node (T.leaf 226) (T.leaf 228)) (T.node (T.leaf 230) (T.leaf 228))))))) (T.node (T.node (T.node (T.node (T.node (T.node (T.leaf 230) (T.leaf 214)) (T.node (T.leaf 228) (T.leaf 252))) (T.node (T.node (T.leaf 203) (T.leaf 242)) (T.node (T.leaf 233) (T.leaf 219)))) (T.node (T.node (T.node (T.leaf 252) (T.leaf 230)) (T.node (T.leaf 215) (T.leaf 243))) (T.node (T.node (T.leaf 238) (T.leaf 242)) (T.node (T.leaf 228) (T.leaf 244))))) (T.node (T.node (T.node (T.node (T.leaf 228) (T.leaf 228)) (T.node (T.leaf 238) (T.leaf 240))) (T.node (T.node (T.leaf 221) (T.leaf 249)) (T.node (T.leaf 228) (T.leaf 238)))) (T.node (T.node (T.node (T.leaf 237) (T.leaf 248)) (T.node (T.leaf 237) (T.leaf 231))) (T.node (T.node (T.leaf 238) (T.leaf 245)) (T.node (T.leaf 250) (T.leaf 234)))))) (T.node (T.node (T.node (T.node (T.node (T.leaf 239) (T.leaf 234)) (T.node (T.leaf 262) (T.leaf 228))) (T.node (T.node (T.leaf 228) (T.leaf 286)) (T.node (T.leaf 239) (T.leaf 235)))) (T.node (T.node (T.node (T.leaf 271) (T.leaf 249)) (T.node (T.leaf 240) (T.leaf 242))) (T.node (T.node (T.leaf 252) (T.leaf 261)) (T.node (T.leaf 233) (T.leaf 253))))) (T.node (T.node (T.node (T.node (T.leaf 268) (T.leaf 243)) (T.node (T.leaf 234) (T.leaf 269))) (T.node (T.node (T.leaf 257) (T.leaf 244)) (T.node (T.leaf 264) (T.leaf 227)))) (T.node (T.node (T.node (T.leaf 273) (T.leaf 273)) (T.node (T.leaf 240) (T.leaf 257))) (T.node (T.node (T.leaf 258) (T.leaf 245)) (T.node (T.leaf 262) (T.leaf 257)))))))))) (T.node (T.node (T.node (T.node (T.node (T.node (T.node (T.node (T.node (T.leaf 256) (T.leaf 0)) (T.leaf 0)) (T.leaf 0)) (T.leaf 0)) (T.leaf 0)) (T.leaf 0)) (T.leaf 0)) (T.leaf 0)) (T.leaf 0))

private def tbl (n : ℕ) : ℕ := qTree.get 10 n

private def checkEntry (n : ℕ) : Bool :=
  if n == 0 then true
  else
    let v := tbl n
    decide (0 < v) &&
    (if n ≤ 2 then v == 1
     else
       let a := tbl (n - 1)
       let b := tbl (n - 2)
       v == (if 0 < a ∧ a < n ∧ 0 < b ∧ b < n then
         tbl (n - a) + tbl (n - b) else 0))

private def checkRange : ℕ → Bool
  | 0 => true
  | n + 1 => checkEntry (n + 1) && checkRange n

private lemma hcheck : checkRange 512 = true := by decide +kernel

private lemma checkRange_spec {N : ℕ} (h : checkRange N = true) :
    ∀ n, 0 < n → n ≤ N → checkEntry n = true := by
  induction N with
  | zero => intro n hn0 hn; omega
  | succ k ih =>
    simp only [checkRange, Bool.and_eq_true] at h
    intro n hn0 hnk
    by_cases heq : n = k + 1
    · subst heq; exact h.1
    · exact ih h.2 n hn0 (by omega)

theorem OMA.solution : OMA.R_Erdos422_erdos_422_variants_well_defined_R1.H1 := by
  refine ⟨q, by rw [q], by rw [q], q_rec, ?_⟩
  have hentry : ∀ n, 0 < n → n ≤ 512 → checkEntry n = true := checkRange_spec hcheck
  have hval : ∀ n, n ≤ 512 → 0 < n → q n = tbl n ∧ 0 < tbl n := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro hn512 hn0
      have hc := hentry n hn0 hn512
      have hne0 : (n == 0) = false := by
        rw [beq_eq_false_iff_ne]
        omega
      simp only [checkEntry, hne0, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true,
        decide_eq_true_eq] at hc
      obtain ⟨hpos, hrest⟩ := hc
      refine ⟨?_, hpos⟩
      by_cases hle2 : n ≤ 2
      · simp only [hle2, ↓reduceIte, beq_iff_eq] at hrest
        interval_cases n
        · simp [q, hrest]
        · simp [q, hrest]
      · simp only [hle2, ↓reduceIte, beq_iff_eq] at hrest
        rw [q_rec n (by omega), hrest]
        have h1 := (ih (n - 1) (by omega) (by omega) (by omega)).1
        have h2 := (ih (n - 2) (by omega) (by omega) (by omega)).1
        rw [h1, h2]
        split_ifs with hcond
        · have ha := (ih (n - tbl (n - 1)) (by omega) (by omega) (by omega)).1
          have hb := (ih (n - tbl (n - 2)) (by omega) (by omega) (by omega)).1
          rw [ha, hb]
        · rfl
  intro n hn0 hn512
  obtain ⟨heq, hpos⟩ := hval n hn512 hn0
  omega
