import OMAStatements.S_oeis_a251132

-- Credit: @Dariusthedoggie
-- Proof: row transfer matrix annihilated by the order-7 recurrence polynomial, giving recurrence, g.f. and closed form, bridged to the Nat.card encoding.

namespace OMA.P251132

open PowerSeries
/-- A `2 X 2` `0..2` subblock does not have diagonal sum greater than antidiagonal maximum. -/
def okBlock (a b c d : Fin 3) : Prop :=
  ¬ (a.val + d.val > max b.val c.val)

instance (a b c d : Fin 3) : Decidable (okBlock a b c d) := by
  unfold okBlock; infer_instance

/-- An `(m + 1) X 4` `0..2` array is valid when every `2 X 2` subblock satisfies `okBlock`. -/
def isValid (m : ℕ) (x : Fin (m + 1) → Fin 4 → Fin 3) : Prop :=
  ∀ i : Fin m, ∀ j : Fin 3,
    okBlock (x i.castSucc j.castSucc) (x i.castSucc j.succ)
      (x i.succ j.castSucc) (x i.succ j.succ)

instance (m : ℕ) (x : Fin (m + 1) → Fin 4 → Fin 3) : Decidable (isValid m x) := by
  unfold isValid; infer_instance

/-- A251132: Number of (n+1) X (3+1) 0..2 arrays with no 2 X 2 subblock having the sum of its diagonal elements greater than the maximum of its antidiagonal elements. -/
def a : ℕ → ℕ
  | 0 => 0
  | n + 1 => (Finset.univ.filter (isValid (n + 1))).card

abbrev Row := Fin 4 → Fin 3

def okRow (r₁ r₂ : Row) : Prop :=
  ∀ j : Fin 3, okBlock (r₁ j.castSucc) (r₁ j.succ) (r₂ j.castSucc) (r₂ j.succ)

instance (r₁ r₂ : Row) : Decidable (okRow r₁ r₂) := by
  unfold okRow; infer_instance

def enc (r : Row) : Fin 81 :=
  ⟨27 * (r 0).val + 9 * (r 1).val + 3 * (r 2).val + (r 3).val, by
    have h0 := (r 0).isLt; have h1 := (r 1).isLt; have h2 := (r 2).isLt; have h3 := (r 3).isLt; omega⟩

def dec (k : Fin 81) : Row := fun c =>
  have hk := k.isLt
  if c.val = 0 then ⟨k.val / 27, by omega⟩
  else if c.val = 1 then ⟨(k.val / 9) % 3, by omega⟩
  else if c.val = 2 then ⟨(k.val / 3) % 3, by omega⟩
  else ⟨k.val % 3, by omega⟩

lemma enc_dec : ∀ k : Fin 81, enc (dec k) = k := by
  intro k; have hk := k.isLt; ext; simp [enc, dec]; try omega

lemma dec_enc : ∀ r : Row, dec (enc r) = r := by
  intro r; ext c
  have h0 := (r 0).isLt; have h1 := (r 1).isLt; have h2 := (r 2).isLt; have h3 := (r 3).isLt
  fin_cases c
  · change (dec (enc r) 0).val = (r 0).val; simp [dec, enc]; try omega
  · change (dec (enc r) 1).val = (r 1).val; simp [dec, enc]; try omega
  · change (dec (enc r) 2).val = (r 2).val; simp [dec, enc]; try omega
  · change (dec (enc r) 3).val = (r 3).val; simp [dec, enc]; try omega

def ok2 (i j : Fin 81) : Prop := okRow (dec i) (dec j)

instance (i j : Fin 81) : Decidable (ok2 i j) := by
  unfold ok2; infer_instance

def adjMask (i : Fin 81) : ℕ := match i.val with
  | 0 => 2233909948714380186091521
  | 1 => 2243373164453127912423427
  | 2 => 2413710471289830388006919
  | 3 => 944547227665962786357256
  | 4 => 949278835535336649523209
  | 5 => 1034447777184066186510363
  | 6 => 302822903639927242620992
  | 7 => 302822903639927242620992
  | 8 => 345407374464292011114569
  | 9 => 118068385443846704595456
  | 10 => 127531565153797143528960
  | 11 => 297573652025526668234240
  | 12 => 37778931862957161709568
  | 13 => 42510539732331024876033
  | 14 => 127531619196993074628099
  | 15 => 0
  | 16 => 0
  | 17 => 42584470824364768498185
  | 18 => 4722366518054017564672
  | 19 => 14167099554162052694016
  | 20 => 33056565626378122952704
  | 21 => 0
  | 22 => 4722366518054017564672
  | 23 => 14167099554162052694016
  | 24 => 0
  | 25 => 0
  | 26 => 4731607904558235517441
  | 27 => 230602315320013094912
  | 28 => 249085088191010045952
  | 29 => 581198539112356773888
  | 30 => 73931091483987804160
  | 31 => 83172477919486279680
  | 32 => 249517433758458839040
  | 33 => 591448731871902433280
  | 34 => 591448731871902433280
  | 35 => 674621209791388712960
  | 36 => 9223372036854775808
  | 37 => 27670116110564327424
  | 38 => 64563604257983430656
  | 39 => 0
  | 40 => 9241386435498475521
  | 41 => 27724159306495426563
  | 42 => 0
  | 43 => 0
  | 44 => 83172477919486279689
  | 45 => 0
  | 46 => 0
  | 47 => 0
  | 48 => 0
  | 49 => 0
  | 50 => 0
  | 51 => 0
  | 52 => 0
  | 53 => 9241386504217952769
  | 54 => 18014398509481984
  | 55 => 54043195528445952
  | 56 => 126100789566373888
  | 57 => 144115188075855872
  | 58 => 162129586585337856
  | 59 => 486388759756013568
  | 60 => 1152921504606846976
  | 61 => 1152921504606846976
  | 62 => 1315051091192184832
  | 63 => 0
  | 64 => 0
  | 65 => 0
  | 66 => 0
  | 67 => 18014398509481984
  | 68 => 54043195528445952
  | 69 => 0
  | 70 => 0
  | 71 => 162129586585337856
  | 72 => 0
  | 73 => 0
  | 74 => 0
  | 75 => 0
  | 76 => 0
  | 77 => 0
  | 78 => 0
  | 79 => 0
  | 80 => 18014398643699713
  | _ => 0

lemma ok2_iff : ∀ i j : Fin 81, ok2 i j ↔ (adjMask i / 2 ^ j.val) % 2 = 1 := by decide +kernel

def step (f : Fin 81 → ℕ) (i : Fin 81) : ℕ :=
  ∑ j : Fin 81, if ok2 i j then f j else 0

def v : ℕ → Fin 81 → ℕ
  | 0, _ => 1
  | m + 1, i => step (v m) i

lemma sum_cons {m : ℕ} (f : (Fin (m + 2) → Row) → ℕ) :
    ∑ x, f x = ∑ r : Row, ∑ y : Fin (m + 1) → Row, f (Fin.cons r y) := by
  rw [← (Fin.consEquiv (fun _ => Row)).sum_comp, Fintype.sum_prod_type]
  rfl

lemma fiber (m : ℕ) (g : (Fin (m + 1) → Row) → ℕ) :
    ∑ y, g y = ∑ i : Fin 81, ∑ y : Fin (m + 1) → Row, if enc (y 0) = i then g y else 0 := by
  trans ∑ y : Fin (m + 1) → Row, ∑ i : Fin 81, if enc (y 0) = i then g y else 0
  · apply Finset.sum_congr rfl
    intro y _
    rw [Finset.sum_eq_single (enc (y 0))]
    · simp
    · intro i _ hi; simp [Ne.symm hi]
    · simp
  · exact Finset.sum_comm

lemma isValid_zero (y : Fin 1 → Row) : isValid 0 y := by
  intro i; exact Fin.elim0 i

lemma isValid_cons (m : ℕ) (r : Row) (y : Fin (m + 1) → Row) :
    isValid (m + 1) (Fin.cons r y) ↔ okRow r (y 0) ∧ isValid m y := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro j
      simpa [Fin.castSucc_zero, Fin.succ_zero_eq_one] using h 0 j
    · intro i j
      simpa using h i.succ j
  · rintro ⟨h0, hy⟩ i j
    refine Fin.cases ?_ (fun i' => ?_) i
    · simpa [Fin.castSucc_zero, Fin.succ_zero_eq_one] using h0 j
    · simpa using hy i' j

lemma v_eq (m : ℕ) (i : Fin 81) :
    v m i = ∑ y : Fin (m + 1) → Row, if enc (y 0) = i ∧ isValid m y then 1 else 0 := by
  induction m generalizing i with
  | zero =>
    rw [v, ← (Equiv.funUnique (Fin 1) Row).symm.sum_comp]
    rw [Finset.sum_eq_single (dec i)]
    · have hu : (Equiv.funUnique (Fin 1) Row).symm (dec i) = fun _ : Fin 1 => dec i := funext fun _ => rfl
      rw [hu]
      simp [enc_dec, isValid_zero]
    · intro r _ hr
      have hne : enc r ≠ i := fun h => hr (by rw [← dec_enc r, h])
      have hu : (Equiv.funUnique (Fin 1) Row).symm r = fun _ : Fin 1 => r := funext fun _ => rfl
      rw [hu]
      simp [hne]
    · simp
  | succ m ih =>
    rw [v, step, sum_cons]
    rw [Finset.sum_eq_single (dec i)]
    · simp only [Fin.cons_zero, enc_dec, true_and, isValid_cons]
      rw [fiber]
      apply Finset.sum_congr rfl
      intro j _
      rw [ih j]
      by_cases h : ok2 i j
      · simp only [h, ↓reduceIte]
        apply Finset.sum_congr rfl
        intro y _
        by_cases hy : enc (y 0) = j
        · have hok : okRow (dec i) (y 0) := by
            rw [← dec_enc (y 0), hy]; exact h
          simp [hy, hok]
        · simp [hy]
      · simp only [h, ↓reduceIte]
        symm
        apply Finset.sum_eq_zero
        intro y _
        by_cases hy : enc (y 0) = j
        · have hnok : ¬ okRow (dec i) (y 0) := by
            rw [← dec_enc (y 0), hy]; exact h
          simp [hy, hnok]
        · simp [hy]
    · intro r _ hr
      have hne : enc r ≠ i := fun h => hr (by rw [← dec_enc r, h])
      apply Finset.sum_eq_zero
      intro y _
      simp [hne]
    · simp

lemma a_succ (n : ℕ) : a (n + 1) = ∑ i : Fin 81, v (n + 1) i := by
  simp only [a, Finset.card_filter]
  rw [fiber]
  apply Finset.sum_congr rfl
  intro i _
  rw [v_eq]
  apply Finset.sum_congr rfl
  intro y _
  split_ifs <;> tauto

def vtab0 (i : Fin 81) : ℕ := match i.val with
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | 7 => 1
  | 8 => 1
  | 9 => 1
  | 10 => 1
  | 11 => 1
  | 12 => 1
  | 13 => 1
  | 14 => 1
  | 15 => 1
  | 16 => 1
  | 17 => 1
  | 18 => 1
  | 19 => 1
  | 20 => 1
  | 21 => 1
  | 22 => 1
  | 23 => 1
  | 24 => 1
  | 25 => 1
  | 26 => 1
  | 27 => 1
  | 28 => 1
  | 29 => 1
  | 30 => 1
  | 31 => 1
  | 32 => 1
  | 33 => 1
  | 34 => 1
  | 35 => 1
  | 36 => 1
  | 37 => 1
  | 38 => 1
  | 39 => 1
  | 40 => 1
  | 41 => 1
  | 42 => 1
  | 43 => 1
  | 44 => 1
  | 45 => 1
  | 46 => 1
  | 47 => 1
  | 48 => 1
  | 49 => 1
  | 50 => 1
  | 51 => 1
  | 52 => 1
  | 53 => 1
  | 54 => 1
  | 55 => 1
  | 56 => 1
  | 57 => 1
  | 58 => 1
  | 59 => 1
  | 60 => 1
  | 61 => 1
  | 62 => 1
  | 63 => 1
  | 64 => 1
  | 65 => 1
  | 66 => 1
  | 67 => 1
  | 68 => 1
  | 69 => 1
  | 70 => 1
  | 71 => 1
  | 72 => 1
  | 73 => 1
  | 74 => 1
  | 75 => 1
  | 76 => 1
  | 77 => 1
  | 78 => 1
  | 79 => 1
  | 80 => 1
  | _ => 0

def vtab1 (i : Fin 81) : ℕ := match i.val with
  | 0 => 15
  | 1 => 21
  | 2 => 30
  | 3 => 8
  | 4 => 14
  | 5 => 26
  | 6 => 6
  | 7 => 6
  | 8 => 18
  | 9 => 6
  | 10 => 10
  | 11 => 15
  | 12 => 1
  | 13 => 8
  | 14 => 16
  | 15 => 0
  | 16 => 0
  | 17 => 14
  | 18 => 3
  | 19 => 6
  | 20 => 9
  | 21 => 0
  | 22 => 3
  | 23 => 6
  | 24 => 0
  | 25 => 0
  | 26 => 9
  | 27 => 5
  | 28 => 8
  | 29 => 12
  | 30 => 3
  | 31 => 6
  | 32 => 12
  | 33 => 3
  | 34 => 3
  | 35 => 9
  | 36 => 1
  | 37 => 2
  | 38 => 3
  | 39 => 0
  | 40 => 4
  | 41 => 8
  | 42 => 0
  | 43 => 0
  | 44 => 8
  | 45 => 0
  | 46 => 0
  | 47 => 0
  | 48 => 0
  | 49 => 0
  | 50 => 0
  | 51 => 0
  | 52 => 0
  | 53 => 6
  | 54 => 1
  | 55 => 2
  | 56 => 3
  | 57 => 1
  | 58 => 2
  | 59 => 4
  | 60 => 1
  | 61 => 1
  | 62 => 3
  | 63 => 0
  | 64 => 0
  | 65 => 0
  | 66 => 0
  | 67 => 1
  | 68 => 2
  | 69 => 0
  | 70 => 0
  | 71 => 2
  | 72 => 0
  | 73 => 0
  | 74 => 0
  | 75 => 0
  | 76 => 0
  | 77 => 0
  | 78 => 0
  | 79 => 0
  | 80 => 3
  | _ => 0

def vtab2 (i : Fin 81) : ℕ := match i.val with
  | 0 => 30
  | 1 => 63
  | 2 => 121
  | 3 => 12
  | 4 => 34
  | 5 => 94
  | 6 => 10
  | 7 => 10
  | 8 => 44
  | 9 => 7
  | 10 => 19
  | 11 => 37
  | 12 => 0
  | 13 => 28
  | 14 => 71
  | 15 => 0
  | 16 => 0
  | 17 => 41
  | 18 => 3
  | 19 => 9
  | 20 => 18
  | 21 => 0
  | 22 => 3
  | 23 => 9
  | 24 => 0
  | 25 => 0
  | 26 => 31
  | 27 => 7
  | 28 => 17
  | 29 => 34
  | 30 => 4
  | 31 => 10
  | 32 => 29
  | 33 => 4
  | 34 => 4
  | 35 => 14
  | 36 => 0
  | 37 => 0
  | 38 => 0
  | 39 => 0
  | 40 => 21
  | 41 => 52
  | 42 => 0
  | 43 => 0
  | 44 => 33
  | 45 => 0
  | 46 => 0
  | 47 => 0
  | 48 => 0
  | 49 => 0
  | 50 => 0
  | 51 => 0
  | 52 => 0
  | 53 => 28
  | 54 => 1
  | 55 => 3
  | 56 => 6
  | 57 => 1
  | 58 => 2
  | 59 => 6
  | 60 => 1
  | 61 => 1
  | 62 => 3
  | 63 => 0
  | 64 => 0
  | 65 => 0
  | 66 => 0
  | 67 => 1
  | 68 => 3
  | 69 => 0
  | 70 => 0
  | 71 => 2
  | 72 => 0
  | 73 => 0
  | 74 => 0
  | 75 => 0
  | 76 => 0
  | 77 => 0
  | 78 => 0
  | 79 => 0
  | 80 => 21
  | _ => 0

def vtab3 (i : Fin 81) : ℕ := match i.val with
  | 0 => 81
  | 1 => 164
  | 2 => 380
  | 3 => 17
  | 4 => 55
  | 5 => 206
  | 6 => 15
  | 7 => 15
  | 8 => 70
  | 9 => 7
  | 10 => 26
  | 11 => 63
  | 12 => 0
  | 13 => 45
  | 14 => 147
  | 15 => 0
  | 16 => 0
  | 17 => 62
  | 18 => 3
  | 19 => 12
  | 20 => 30
  | 21 => 0
  | 22 => 3
  | 23 => 12
  | 24 => 0
  | 25 => 0
  | 26 => 48
  | 27 => 9
  | 28 => 29
  | 29 => 72
  | 30 => 5
  | 31 => 13
  | 32 => 46
  | 33 => 5
  | 34 => 5
  | 35 => 18
  | 36 => 0
  | 37 => 0
  | 38 => 0
  | 39 => 0
  | 40 => 38
  | 41 => 121
  | 42 => 0
  | 43 => 0
  | 44 => 55
  | 45 => 0
  | 46 => 0
  | 47 => 0
  | 48 => 0
  | 49 => 0
  | 50 => 0
  | 51 => 0
  | 52 => 0
  | 53 => 45
  | 54 => 1
  | 55 => 4
  | 56 => 10
  | 57 => 1
  | 58 => 2
  | 59 => 7
  | 60 => 1
  | 61 => 1
  | 62 => 3
  | 63 => 0
  | 64 => 0
  | 65 => 0
  | 66 => 0
  | 67 => 1
  | 68 => 4
  | 69 => 0
  | 70 => 0
  | 71 => 2
  | 72 => 0
  | 73 => 0
  | 74 => 0
  | 75 => 0
  | 76 => 0
  | 77 => 0
  | 78 => 0
  | 79 => 0
  | 80 => 38
  | _ => 0

def vtab4 (i : Fin 81) : ℕ := match i.val with
  | 0 => 168
  | 1 => 365
  | 2 => 952
  | 3 => 23
  | 4 => 114
  | 5 => 420
  | 6 => 21
  | 7 => 21
  | 8 => 135
  | 9 => 7
  | 10 => 33
  | 11 => 96
  | 12 => 0
  | 13 => 98
  | 14 => 321
  | 15 => 0
  | 16 => 0
  | 17 => 121
  | 18 => 3
  | 19 => 15
  | 20 => 45
  | 21 => 0
  | 22 => 3
  | 23 => 15
  | 24 => 0
  | 25 => 0
  | 26 => 101
  | 27 => 11
  | 28 => 44
  | 29 => 130
  | 30 => 6
  | 31 => 16
  | 32 => 65
  | 33 => 6
  | 34 => 6
  | 35 => 22
  | 36 => 0
  | 37 => 0
  | 38 => 0
  | 39 => 0
  | 40 => 91
  | 41 => 288
  | 42 => 0
  | 43 => 0
  | 44 => 114
  | 45 => 0
  | 46 => 0
  | 47 => 0
  | 48 => 0
  | 49 => 0
  | 50 => 0
  | 51 => 0
  | 52 => 0
  | 53 => 98
  | 54 => 1
  | 55 => 5
  | 56 => 15
  | 57 => 1
  | 58 => 2
  | 59 => 8
  | 60 => 1
  | 61 => 1
  | 62 => 3
  | 63 => 0
  | 64 => 0
  | 65 => 0
  | 66 => 0
  | 67 => 1
  | 68 => 5
  | 69 => 0
  | 70 => 0
  | 71 => 2
  | 72 => 0
  | 73 => 0
  | 74 => 0
  | 75 => 0
  | 76 => 0
  | 77 => 0
  | 78 => 0
  | 79 => 0
  | 80 => 91
  | _ => 0

def vtab5 (i : Fin 81) : ℕ := match i.val with
  | 0 => 363
  | 1 => 777
  | 2 => 2167
  | 3 => 30
  | 4 => 210
  | 5 => 848
  | 6 => 28
  | 7 => 28
  | 8 => 238
  | 9 => 7
  | 10 => 40
  | 11 => 136
  | 12 => 0
  | 13 => 187
  | 14 => 634
  | 15 => 0
  | 16 => 0
  | 17 => 217
  | 18 => 3
  | 19 => 18
  | 20 => 63
  | 21 => 0
  | 22 => 3
  | 23 => 18
  | 24 => 0
  | 25 => 0
  | 26 => 190
  | 27 => 13
  | 28 => 62
  | 29 => 212
  | 30 => 7
  | 31 => 19
  | 32 => 87
  | 33 => 7
  | 34 => 7
  | 35 => 26
  | 36 => 0
  | 37 => 0
  | 38 => 0
  | 39 => 0
  | 40 => 180
  | 41 => 594
  | 42 => 0
  | 43 => 0
  | 44 => 210
  | 45 => 0
  | 46 => 0
  | 47 => 0
  | 48 => 0
  | 49 => 0
  | 50 => 0
  | 51 => 0
  | 52 => 0
  | 53 => 187
  | 54 => 1
  | 55 => 6
  | 56 => 21
  | 57 => 1
  | 58 => 2
  | 59 => 9
  | 60 => 1
  | 61 => 1
  | 62 => 3
  | 63 => 0
  | 64 => 0
  | 65 => 0
  | 66 => 0
  | 67 => 1
  | 68 => 6
  | 69 => 0
  | 70 => 0
  | 71 => 2
  | 72 => 0
  | 73 => 0
  | 74 => 0
  | 75 => 0
  | 76 => 0
  | 77 => 0
  | 78 => 0
  | 79 => 0
  | 80 => 180
  | _ => 0

def vtab6 (i : Fin 81) : ℕ := match i.val with
  | 0 => 738
  | 1 => 1583
  | 2 => 4583
  | 3 => 38
  | 4 => 415
  | 5 => 1672
  | 6 => 36
  | 7 => 36
  | 8 => 451
  | 9 => 7
  | 10 => 47
  | 11 => 183
  | 12 => 0
  | 13 => 384
  | 14 => 1269
  | 15 => 0
  | 16 => 0
  | 17 => 422
  | 18 => 3
  | 19 => 21
  | 20 => 84
  | 21 => 0
  | 22 => 3
  | 23 => 21
  | 24 => 0
  | 25 => 0
  | 26 => 387
  | 27 => 15
  | 28 => 83
  | 29 => 322
  | 30 => 8
  | 31 => 22
  | 32 => 112
  | 33 => 8
  | 34 => 8
  | 35 => 30
  | 36 => 0
  | 37 => 0
  | 38 => 0
  | 39 => 0
  | 40 => 377
  | 41 => 1222
  | 42 => 0
  | 43 => 0
  | 44 => 415
  | 45 => 0
  | 46 => 0
  | 47 => 0
  | 48 => 0
  | 49 => 0
  | 50 => 0
  | 51 => 0
  | 52 => 0
  | 53 => 384
  | 54 => 1
  | 55 => 7
  | 56 => 28
  | 57 => 1
  | 58 => 2
  | 59 => 10
  | 60 => 1
  | 61 => 1
  | 62 => 3
  | 63 => 0
  | 64 => 0
  | 65 => 0
  | 66 => 0
  | 67 => 1
  | 68 => 7
  | 69 => 0
  | 70 => 0
  | 71 => 2
  | 72 => 0
  | 73 => 0
  | 74 => 0
  | 75 => 0
  | 76 => 0
  | 77 => 0
  | 78 => 0
  | 79 => 0
  | 80 => 377
  | _ => 0

def vtab7 (i : Fin 81) : ℕ := match i.val with
  | 0 => 1509
  | 1 => 3182
  | 2 => 9344
  | 3 => 47
  | 4 => 801
  | 5 => 3291
  | 6 => 45
  | 7 => 45
  | 8 => 846
  | 9 => 7
  | 10 => 54
  | 11 => 237
  | 12 => 0
  | 13 => 761
  | 14 => 2481
  | 15 => 0
  | 16 => 0
  | 17 => 808
  | 18 => 3
  | 19 => 24
  | 20 => 108
  | 21 => 0
  | 22 => 3
  | 23 => 24
  | 24 => 0
  | 25 => 0
  | 26 => 764
  | 27 => 17
  | 28 => 107
  | 29 => 464
  | 30 => 9
  | 31 => 25
  | 32 => 140
  | 33 => 9
  | 34 => 9
  | 35 => 34
  | 36 => 0
  | 37 => 0
  | 38 => 0
  | 39 => 0
  | 40 => 754
  | 41 => 2427
  | 42 => 0
  | 43 => 0
  | 44 => 801
  | 45 => 0
  | 46 => 0
  | 47 => 0
  | 48 => 0
  | 49 => 0
  | 50 => 0
  | 51 => 0
  | 52 => 0
  | 53 => 761
  | 54 => 1
  | 55 => 8
  | 56 => 36
  | 57 => 1
  | 58 => 2
  | 59 => 11
  | 60 => 1
  | 61 => 1
  | 62 => 3
  | 63 => 0
  | 64 => 0
  | 65 => 0
  | 66 => 0
  | 67 => 1
  | 68 => 8
  | 69 => 0
  | 70 => 0
  | 71 => 2
  | 72 => 0
  | 73 => 0
  | 74 => 0
  | 75 => 0
  | 76 => 0
  | 77 => 0
  | 78 => 0
  | 79 => 0
  | 80 => 754
  | _ => 0

def vtab8 (i : Fin 81) : ℕ := match i.val with
  | 0 => 3036
  | 1 => 6333
  | 2 => 18612
  | 3 => 57
  | 4 => 1584
  | 5 => 6464
  | 6 => 55
  | 7 => 55
  | 8 => 1639
  | 9 => 7
  | 10 => 61
  | 11 => 298
  | 12 => 0
  | 13 => 1534
  | 14 => 4885
  | 15 => 0
  | 16 => 0
  | 17 => 1591
  | 18 => 3
  | 19 => 27
  | 20 => 135
  | 21 => 0
  | 22 => 3
  | 23 => 27
  | 24 => 0
  | 25 => 0
  | 26 => 1537
  | 27 => 19
  | 28 => 134
  | 29 => 642
  | 30 => 10
  | 31 => 28
  | 32 => 171
  | 33 => 10
  | 34 => 10
  | 35 => 38
  | 36 => 0
  | 37 => 0
  | 38 => 0
  | 39 => 0
  | 40 => 1527
  | 41 => 4824
  | 42 => 0
  | 43 => 0
  | 44 => 1584
  | 45 => 0
  | 46 => 0
  | 47 => 0
  | 48 => 0
  | 49 => 0
  | 50 => 0
  | 51 => 0
  | 52 => 0
  | 53 => 1534
  | 54 => 1
  | 55 => 9
  | 56 => 45
  | 57 => 1
  | 58 => 2
  | 59 => 12
  | 60 => 1
  | 61 => 1
  | 62 => 3
  | 63 => 0
  | 64 => 0
  | 65 => 0
  | 66 => 0
  | 67 => 1
  | 68 => 9
  | 69 => 0
  | 70 => 0
  | 71 => 2
  | 72 => 0
  | 73 => 0
  | 74 => 0
  | 75 => 0
  | 76 => 0
  | 77 => 0
  | 78 => 0
  | 79 => 0
  | 80 => 1527
  | _ => 0

def vtab9 (i : Fin 81) : ℕ := match i.val with
  | 0 => 6111
  | 1 => 12587
  | 2 => 36719
  | 3 => 68
  | 4 => 3124
  | 5 => 12742
  | 6 => 66
  | 7 => 66
  | 8 => 3190
  | 9 => 7
  | 10 => 68
  | 11 => 366
  | 12 => 0
  | 13 => 3063
  | 14 => 9600
  | 15 => 0
  | 16 => 0
  | 17 => 3131
  | 18 => 3
  | 19 => 30
  | 20 => 165
  | 21 => 0
  | 22 => 3
  | 23 => 30
  | 24 => 0
  | 25 => 0
  | 26 => 3066
  | 27 => 21
  | 28 => 164
  | 29 => 860
  | 30 => 11
  | 31 => 31
  | 32 => 205
  | 33 => 11
  | 34 => 11
  | 35 => 42
  | 36 => 0
  | 37 => 0
  | 38 => 0
  | 39 => 0
  | 40 => 3056
  | 41 => 9532
  | 42 => 0
  | 43 => 0
  | 44 => 3124
  | 45 => 0
  | 46 => 0
  | 47 => 0
  | 48 => 0
  | 49 => 0
  | 50 => 0
  | 51 => 0
  | 52 => 0
  | 53 => 3063
  | 54 => 1
  | 55 => 10
  | 56 => 55
  | 57 => 1
  | 58 => 2
  | 59 => 13
  | 60 => 1
  | 61 => 1
  | 62 => 3
  | 63 => 0
  | 64 => 0
  | 65 => 0
  | 66 => 0
  | 67 => 1
  | 68 => 10
  | 69 => 0
  | 70 => 0
  | 71 => 2
  | 72 => 0
  | 73 => 0
  | 74 => 0
  | 75 => 0
  | 76 => 0
  | 77 => 0
  | 78 => 0
  | 79 => 0
  | 80 => 3056
  | _ => 0

def vtab10 (i : Fin 81) : ℕ := match i.val with
  | 0 => 12246
  | 1 => 25007
  | 2 => 72183
  | 3 => 80
  | 4 => 6213
  | 5 => 25188
  | 6 => 78
  | 7 => 78
  | 8 => 6291
  | 9 => 7
  | 10 => 75
  | 11 => 441
  | 12 => 0
  | 13 => 6140
  | 14 => 18969
  | 15 => 0
  | 16 => 0
  | 17 => 6220
  | 18 => 3
  | 19 => 33
  | 20 => 198
  | 21 => 0
  | 22 => 3
  | 23 => 33
  | 24 => 0
  | 25 => 0
  | 26 => 6143
  | 27 => 23
  | 28 => 197
  | 29 => 1122
  | 30 => 12
  | 31 => 34
  | 32 => 242
  | 33 => 12
  | 34 => 12
  | 35 => 46
  | 36 => 0
  | 37 => 0
  | 38 => 0
  | 39 => 0
  | 40 => 6133
  | 41 => 18894
  | 42 => 0
  | 43 => 0
  | 44 => 6213
  | 45 => 0
  | 46 => 0
  | 47 => 0
  | 48 => 0
  | 49 => 0
  | 50 => 0
  | 51 => 0
  | 52 => 0
  | 53 => 6140
  | 54 => 1
  | 55 => 11
  | 56 => 66
  | 57 => 1
  | 58 => 2
  | 59 => 14
  | 60 => 1
  | 61 => 1
  | 62 => 3
  | 63 => 0
  | 64 => 0
  | 65 => 0
  | 66 => 0
  | 67 => 1
  | 68 => 11
  | 69 => 0
  | 70 => 0
  | 71 => 2
  | 72 => 0
  | 73 => 0
  | 74 => 0
  | 75 => 0
  | 76 => 0
  | 77 => 0
  | 78 => 0
  | 79 => 0
  | 80 => 6133
  | _ => 0

def vtab11 (i : Fin 81) : ℕ := match i.val with
  | 0 => 24537
  | 1 => 49752
  | 2 => 142028
  | 3 => 93
  | 4 => 12363
  | 5 => 49961
  | 6 => 91
  | 7 => 91
  | 8 => 12454
  | 9 => 7
  | 10 => 82
  | 11 => 523
  | 12 => 0
  | 13 => 12277
  | 14 => 37567
  | 15 => 0
  | 16 => 0
  | 17 => 12370
  | 18 => 3
  | 19 => 36
  | 20 => 234
  | 21 => 0
  | 22 => 3
  | 23 => 36
  | 24 => 0
  | 25 => 0
  | 26 => 12280
  | 27 => 25
  | 28 => 233
  | 29 => 1432
  | 30 => 13
  | 31 => 37
  | 32 => 282
  | 33 => 13
  | 34 => 13
  | 35 => 50
  | 36 => 0
  | 37 => 0
  | 38 => 0
  | 39 => 0
  | 40 => 12270
  | 41 => 37485
  | 42 => 0
  | 43 => 0
  | 44 => 12363
  | 45 => 0
  | 46 => 0
  | 47 => 0
  | 48 => 0
  | 49 => 0
  | 50 => 0
  | 51 => 0
  | 52 => 0
  | 53 => 12277
  | 54 => 1
  | 55 => 12
  | 56 => 78
  | 57 => 1
  | 58 => 2
  | 59 => 15
  | 60 => 1
  | 61 => 1
  | 62 => 3
  | 63 => 0
  | 64 => 0
  | 65 => 0
  | 66 => 0
  | 67 => 1
  | 68 => 12
  | 69 => 0
  | 70 => 0
  | 71 => 2
  | 72 => 0
  | 73 => 0
  | 74 => 0
  | 75 => 0
  | 76 => 0
  | 77 => 0
  | 78 => 0
  | 79 => 0
  | 80 => 12270
  | _ => 0

lemma v_0 : ∀ i : Fin 81, v 0 i = vtab0 i := by decide +kernel
lemma v_1 : ∀ i : Fin 81, v 1 i = vtab1 i := by
  intro i; rw [show (1 : ℕ) = 0 + 1 from rfl, v, step]; simp only [v_0, ok2_iff]; revert i; decide +kernel
lemma v_2 : ∀ i : Fin 81, v 2 i = vtab2 i := by
  intro i; rw [show (2 : ℕ) = 1 + 1 from rfl, v, step]; simp only [v_1, ok2_iff]; revert i; decide +kernel
lemma v_3 : ∀ i : Fin 81, v 3 i = vtab3 i := by
  intro i; rw [show (3 : ℕ) = 2 + 1 from rfl, v, step]; simp only [v_2, ok2_iff]; revert i; decide +kernel
lemma v_4 : ∀ i : Fin 81, v 4 i = vtab4 i := by
  intro i; rw [show (4 : ℕ) = 3 + 1 from rfl, v, step]; simp only [v_3, ok2_iff]; revert i; decide +kernel
lemma v_5 : ∀ i : Fin 81, v 5 i = vtab5 i := by
  intro i; rw [show (5 : ℕ) = 4 + 1 from rfl, v, step]; simp only [v_4, ok2_iff]; revert i; decide +kernel
lemma v_6 : ∀ i : Fin 81, v 6 i = vtab6 i := by
  intro i; rw [show (6 : ℕ) = 5 + 1 from rfl, v, step]; simp only [v_5, ok2_iff]; revert i; decide +kernel
lemma v_7 : ∀ i : Fin 81, v 7 i = vtab7 i := by
  intro i; rw [show (7 : ℕ) = 6 + 1 from rfl, v, step]; simp only [v_6, ok2_iff]; revert i; decide +kernel
lemma v_8 : ∀ i : Fin 81, v 8 i = vtab8 i := by
  intro i; rw [show (8 : ℕ) = 7 + 1 from rfl, v, step]; simp only [v_7, ok2_iff]; revert i; decide +kernel
lemma v_9 : ∀ i : Fin 81, v 9 i = vtab9 i := by
  intro i; rw [show (9 : ℕ) = 8 + 1 from rfl, v, step]; simp only [v_8, ok2_iff]; revert i; decide +kernel
lemma v_10 : ∀ i : Fin 81, v 10 i = vtab10 i := by
  intro i; rw [show (10 : ℕ) = 9 + 1 from rfl, v, step]; simp only [v_9, ok2_iff]; revert i; decide +kernel
lemma v_11 : ∀ i : Fin 81, v 11 i = vtab11 i := by
  intro i; rw [show (11 : ℕ) = 10 + 1 from rfl, v, step]; simp only [v_10, ok2_iff]; revert i; decide +kernel

def err (m : ℕ) (i : Fin 81) : ℤ :=
  (v (m + 7) i : ℤ) - 6 * (v (m + 6) i : ℤ) + 13 * (v (m + 5) i : ℤ) - 10 * (v (m + 4) i : ℤ) - 5 * (v (m + 3) i : ℤ) + 14 * (v (m + 2) i : ℤ) - 9 * (v (m + 1) i : ℤ) + 2 * (v m i : ℤ)

lemma err_base : ∀ i : Fin 81, err 4 i = 0 := by
  intro i
  change (v 11 i : ℤ) - 6 * (v 10 i : ℤ) + 13 * (v 9 i : ℤ) - 10 * (v 8 i : ℤ) - 5 * (v 7 i : ℤ) + 14 * (v 6 i : ℤ) - 9 * (v 5 i : ℤ) + 2 * (v 4 i : ℤ) = 0
  simp only [v_11, v_10, v_9, v_8, v_7, v_6, v_5, v_4]
  revert i; decide +kernel

lemma err_succ (m : ℕ) (i : Fin 81) :
    err (m + 1) i = ∑ j : Fin 81, if ok2 i j then err m j else 0 := by
  have hV : ∀ r, (v (r + 1) i : ℤ) = ∑ j : Fin 81, if ok2 i j then (v r j : ℤ) else 0 := by
    intro r; rw [v, step]; simp only [Nat.cast_sum, apply_ite Nat.cast, Nat.cast_zero]
  unfold err
  simp only [hV]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> ring

lemma err_ge (m : ℕ) (i : Fin 81) : err (m + 4) i = 0 := by
  induction m generalizing i with
  | zero => simpa using err_base i
  | succ m ih =>
    rw [show m + 1 + 4 = (m + 4) + 1 by omega, err_succ]
    exact Finset.sum_eq_zero (fun j _ => by simp [ih j])

lemma a_rec_ge (m : ℕ) :
    (a (m + 11) : ℤ) = 6 * a (m + 10) - 13 * a (m + 9) + 10 * a (m + 8) + 5 * a (m + 7) - 14 * a (m + 6) + 9 * a (m + 5) - 2 * a (m + 4) := by
  have h : ∑ i : Fin 81, err (m + 4) i = 0 :=
    Finset.sum_eq_zero (fun i _ => err_ge m i)
  unfold err at h
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at h
  have hsum : ∀ r : ℕ, (∑ i : Fin 81, (v (m + 4 + r) i : ℤ)) = (a (m + 4 + r) : ℤ) := by
    intro r
    have h1 : m + 4 + r = (m + 3 + r) + 1 := by omega
    rw [h1, a_succ, Nat.cast_sum]
  have hsum0 : (∑ i : Fin 81, (v (m + 4) i : ℤ)) = (a (m + 4) : ℤ) := by
    simpa only [Nat.add_zero] using hsum 0
  simp only [hsum, hsum0] at h
  have h2_1 : m + 4 + 1 = m + 5 := by omega
  have h2_2 : m + 4 + 2 = m + 6 := by omega
  have h2_3 : m + 4 + 3 = m + 7 := by omega
  have h2_4 : m + 4 + 4 = m + 8 := by omega
  have h2_5 : m + 4 + 5 = m + 9 := by omega
  have h2_6 : m + 4 + 6 = m + 10 := by omega
  have h2_7 : m + 4 + 7 = m + 11 := by omega
  simp only [h2_1, h2_2, h2_3, h2_4, h2_5, h2_6, h2_7] at h
  linarith


lemma a_0 : a 0 = 0 := rfl
lemma a_1 : a 1 = 369 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, a_succ]
  change ∑ i : Fin 81, v 1 i = 369
  simp only [v_1]; decide +kernel
lemma a_2 : a 2 = 1002 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, a_succ]
  change ∑ i : Fin 81, v 2 i = 1002
  simp only [v_2]; decide +kernel
lemma a_3 : a 3 = 1997 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, a_succ]
  change ∑ i : Fin 81, v 3 i = 1997
  simp only [v_3]; decide +kernel
lemma a_4 : a 4 = 4110 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, a_succ]
  change ∑ i : Fin 81, v 4 i = 4110
  simp only [v_4]; decide +kernel
lemma a_5 : a 5 = 8050 := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, a_succ]
  change ∑ i : Fin 81, v 5 i = 8050
  simp only [v_5]; decide +kernel
lemma a_6 : a 6 = 15830 := by
  rw [show (6 : ℕ) = 5 + 1 from rfl, a_succ]
  change ∑ i : Fin 81, v 6 i = 15830
  simp only [v_6]; decide +kernel
lemma a_7 : a 7 = 30770 := by
  rw [show (7 : ℕ) = 6 + 1 from rfl, a_succ]
  change ∑ i : Fin 81, v 7 i = 30770
  simp only [v_7]; decide +kernel
lemma a_8 : a 8 = 60088 := by
  rw [show (8 : ℕ) = 7 + 1 from rfl, a_succ]
  change ∑ i : Fin 81, v 8 i = 60088
  simp only [v_8]; decide +kernel
lemma a_9 : a 9 = 117492 := by
  rw [show (9 : ℕ) = 8 + 1 from rfl, a_succ]
  change ∑ i : Fin 81, v 9 i = 117492
  simp only [v_9]; decide +kernel
lemma a_10 : a 10 = 230956 := by
  rw [show (10 : ℕ) = 9 + 1 from rfl, a_succ]
  change ∑ i : Fin 81, v 10 i = 230956
  simp only [v_10]; decide +kernel

def cf (n : ℕ) : ℚ :=
  (36 * (-5 + 9 * (-1 : ℚ) ^ n + 9 * (2 : ℚ) ^ (3 + n)) + 202 * (n : ℚ) + 151 * (n : ℚ) ^ 2 + 50 * (n : ℚ) ^ 3 + 5 * (n : ℚ) ^ 4) / 12


theorem main_proof_ours :
    (∀ n : ℕ, 11 ≤ n → (a n : ℤ) = 6 * a (n - 1) - 13 * a (n - 2) + 10 * a (n - 3) + 5 * a (n - 4) - 14 * a (n - 5) + 9 * a (n - 6) - 2 * a (n - 7)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 5 * (1 + X) * (1 - 2 * X)) =
      X * (369 - 1212 * X + 782 * X ^ 2 + 1464 * X ^ 3 - 2514 * X ^ 4 + 1146 * X ^ 5 + 62 * X ^ 6 - 114 * X ^ 7 - 5 * X ^ 8 + 2 * X ^ 9)) ∧
    (∀ n : ℕ, 4 ≤ n → (a n : ℚ) = (36 * (-5 + 9 * (-1 : ℚ) ^ n + 9 * (2 : ℚ) ^ (3 + n)) + 202 * (n : ℚ) + 151 * (n : ℚ) ^ 2 + 50 * (n : ℚ) ^ 3 + 5 * (n : ℚ) ^ 4) / 12) := by
  have hrec : ∀ n : ℕ, 11 ≤ n → (a n : ℤ) = 6 * a (n - 1) - 13 * a (n - 2) + 10 * a (n - 3) + 5 * a (n - 4) - 14 * a (n - 5) + 9 * a (n - 6) - 2 * a (n - 7) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 11 := ⟨n - 11, by omega⟩
    simpa using a_rec_ge m
  have hgf : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 5 * (1 + X) * (1 - 2 * X)) =
      X * (369 - 1212 * X + 782 * X ^ 2 + 1464 * X ^ 3 - 2514 * X ^ 4 + 1146 * X ^ 5 + 62 * X ^ 6 - 114 * X ^ 7 - 5 * X ^ 8 + 2 * X ^ 9) := by
    have hl : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 5 * (1 + X) * (1 - 2 * X)) =
        PowerSeries.mk (fun n => (a n : ℚ))
        - C (6 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 1)
        + C (13 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 2)
        - C (10 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 3)
        - C (5 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 4)
        + C (14 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 5)
        - C (9 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 6)
        + C (2 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 7) := by
      simp only [map_ofNat, map_one]; ring
    have hr : (X * (369 - 1212 * X + 782 * X ^ 2 + 1464 * X ^ 3 - 2514 * X ^ 4 + 1146 * X ^ 5 + 62 * X ^ 6 - 114 * X ^ 7 - 5 * X ^ 8 + 2 * X ^ 9) : PowerSeries ℚ) =
        C (369 : ℚ) * X ^ 1 - C (1212 : ℚ) * X ^ 2 + C (782 : ℚ) * X ^ 3 + C (1464 : ℚ) * X ^ 4 - C (2514 : ℚ) * X ^ 5 + C (1146 : ℚ) * X ^ 6 + C (62 : ℚ) * X ^ 7 - C (114 : ℚ) * X ^ 8 - C (5 : ℚ) * X ^ 9 + C (2 : ℚ) * X ^ 10 := by
      simp only [map_ofNat, map_one]; ring
    rw [hl, hr]
    ext n
    simp only [map_sub, map_add, map_neg, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
    rcases Nat.lt_or_ge n 11 with hn | hn
    · interval_cases n <;> simp [a_0, a_1, a_2, a_3, a_4, a_5, a_6, a_7, a_8, a_9, a_10] <;> try norm_num
    · have hq : (a n : ℚ) = 6 * a (n - 1) - 13 * a (n - 2) + 10 * a (n - 3) + 5 * a (n - 4) - 14 * a (n - 5) + 9 * a (n - 6) - 2 * a (n - 7) := by
        exact_mod_cast hrec n (by omega)
      have c1 : 1 ≤ n := by omega
      have c2 : 2 ≤ n := by omega
      have c3 : 3 ≤ n := by omega
      have c4 : 4 ≤ n := by omega
      have c5 : 5 ≤ n := by omega
      have c6 : 6 ≤ n := by omega
      have c7 : 7 ≤ n := by omega
      have e1 : n - 1 ≠ 0 := by omega
      have e2 : n - 2 ≠ 0 := by omega
      have e3 : n - 3 ≠ 0 := by omega
      have e4 : n - 4 ≠ 0 := by omega
      have e5 : n - 5 ≠ 0 := by omega
      have e6 : n - 6 ≠ 0 := by omega
      have e7 : n - 7 ≠ 0 := by omega
      have e8 : n - 8 ≠ 0 := by omega
      have e9 : n - 9 ≠ 0 := by omega
      have e10 : n - 10 ≠ 0 := by omega
      simp only [c1, c2, c3, c4, c5, c6, c7, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, coeff_C, if_true, if_false, ite_self]
      rw [hq]; ring
  have hcf : ∀ n : ℕ, 4 ≤ n → (a n : ℚ) = (36 * (-5 + 9 * (-1 : ℚ) ^ n + 9 * (2 : ℚ) ^ (3 + n)) + 202 * (n : ℚ) + 151 * (n : ℚ) ^ 2 + 50 * (n : ℚ) ^ 3 + 5 * (n : ℚ) ^ 4) / 12 := by
    have hb_4 : (a 4 : ℚ) = cf 4 := by
      rw [a_4]; unfold cf
      push_cast
      norm_num
    have hb_5 : (a 5 : ℚ) = cf 5 := by
      rw [a_5]; unfold cf
      push_cast
      norm_num
    have hb_6 : (a 6 : ℚ) = cf 6 := by
      rw [a_6]; unfold cf
      push_cast
      norm_num
    have hb_7 : (a 7 : ℚ) = cf 7 := by
      rw [a_7]; unfold cf
      push_cast
      norm_num
    have hb_8 : (a 8 : ℚ) = cf 8 := by
      rw [a_8]; unfold cf
      push_cast
      norm_num
    have hb_9 : (a 9 : ℚ) = cf 9 := by
      rw [a_9]; unfold cf
      push_cast
      norm_num
    have hb_10 : (a 10 : ℚ) = cf 10 := by
      rw [a_10]; unfold cf
      push_cast
      norm_num
    have cf_rec : ∀ m : ℕ, cf (m + 11) = 6 * cf (m + 10) - 13 * cf (m + 9) + 10 * cf (m + 8) + 5 * cf (m + 7) - 14 * cf (m + 6) + 9 * cf (m + 5) - 2 * cf (m + 4) := by
      intro m
      unfold cf
      have hp_a_1 : (-1 : ℚ) ^ (m + 5) = (-1 : ℚ) ^ (m + 4) * (-1 : ℚ) ^ 1 := by
        rw [show m + 5 = (m + 4) + 1 by omega, pow_add]
      have hp_a_2 : (-1 : ℚ) ^ (m + 6) = (-1 : ℚ) ^ (m + 4) * (-1 : ℚ) ^ 2 := by
        rw [show m + 6 = (m + 4) + 2 by omega, pow_add]
      have hp_a_3 : (-1 : ℚ) ^ (m + 7) = (-1 : ℚ) ^ (m + 4) * (-1 : ℚ) ^ 3 := by
        rw [show m + 7 = (m + 4) + 3 by omega, pow_add]
      have hp_a_4 : (-1 : ℚ) ^ (m + 8) = (-1 : ℚ) ^ (m + 4) * (-1 : ℚ) ^ 4 := by
        rw [show m + 8 = (m + 4) + 4 by omega, pow_add]
      have hp_a_5 : (-1 : ℚ) ^ (m + 9) = (-1 : ℚ) ^ (m + 4) * (-1 : ℚ) ^ 5 := by
        rw [show m + 9 = (m + 4) + 5 by omega, pow_add]
      have hp_a_6 : (-1 : ℚ) ^ (m + 10) = (-1 : ℚ) ^ (m + 4) * (-1 : ℚ) ^ 6 := by
        rw [show m + 10 = (m + 4) + 6 by omega, pow_add]
      have hp_a_7 : (-1 : ℚ) ^ (m + 11) = (-1 : ℚ) ^ (m + 4) * (-1 : ℚ) ^ 7 := by
        rw [show m + 11 = (m + 4) + 7 by omega, pow_add]
      have hp_t_1 : (2 : ℚ) ^ (3 + (m + 5)) = (2 : ℚ) ^ (3 + (m + 4)) * (2 : ℚ) ^ 1 := by
        rw [show 3 + (m + 5) = (3 + (m + 4)) + 1 by omega, pow_add]
      have hp_t_2 : (2 : ℚ) ^ (3 + (m + 6)) = (2 : ℚ) ^ (3 + (m + 4)) * (2 : ℚ) ^ 2 := by
        rw [show 3 + (m + 6) = (3 + (m + 4)) + 2 by omega, pow_add]
      have hp_t_3 : (2 : ℚ) ^ (3 + (m + 7)) = (2 : ℚ) ^ (3 + (m + 4)) * (2 : ℚ) ^ 3 := by
        rw [show 3 + (m + 7) = (3 + (m + 4)) + 3 by omega, pow_add]
      have hp_t_4 : (2 : ℚ) ^ (3 + (m + 8)) = (2 : ℚ) ^ (3 + (m + 4)) * (2 : ℚ) ^ 4 := by
        rw [show 3 + (m + 8) = (3 + (m + 4)) + 4 by omega, pow_add]
      have hp_t_5 : (2 : ℚ) ^ (3 + (m + 9)) = (2 : ℚ) ^ (3 + (m + 4)) * (2 : ℚ) ^ 5 := by
        rw [show 3 + (m + 9) = (3 + (m + 4)) + 5 by omega, pow_add]
      have hp_t_6 : (2 : ℚ) ^ (3 + (m + 10)) = (2 : ℚ) ^ (3 + (m + 4)) * (2 : ℚ) ^ 6 := by
        rw [show 3 + (m + 10) = (3 + (m + 4)) + 6 by omega, pow_add]
      have hp_t_7 : (2 : ℚ) ^ (3 + (m + 11)) = (2 : ℚ) ^ (3 + (m + 4)) * (2 : ℚ) ^ 7 := by
        rw [show 3 + (m + 11) = (3 + (m + 4)) + 7 by omega, pow_add]
      simp only [hp_a_1, hp_a_2, hp_a_3, hp_a_4, hp_a_5, hp_a_6, hp_a_7, hp_t_1, hp_t_2, hp_t_3, hp_t_4, hp_t_5, hp_t_6, hp_t_7]
      generalize (-1 : ℚ) ^ (m + 4) = Xa
      generalize (2 : ℚ) ^ (3 + (m + 4)) = Xt
      push_cast
      ring
    have hR : ∀ m : ℕ,
        (a (m + 4) : ℚ) = cf (m + 4) ∧
        (a (m + 5) : ℚ) = cf (m + 5) ∧
        (a (m + 6) : ℚ) = cf (m + 6) ∧
        (a (m + 7) : ℚ) = cf (m + 7) ∧
        (a (m + 8) : ℚ) = cf (m + 8) ∧
        (a (m + 9) : ℚ) = cf (m + 9) ∧
        (a (m + 10) : ℚ) = cf (m + 10) := by
      intro m
      induction m with
      | zero =>
        simp only [Nat.zero_add]
        exact ⟨hb_4, hb_5, hb_6, hb_7, hb_8, hb_9, hb_10⟩
      | succ m ih =>
        obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := ih
        refine ⟨(by simpa only [show m + 1 + 4 = m + 5 by omega] using h1), (by simpa only [show m + 1 + 5 = m + 6 by omega] using h2), (by simpa only [show m + 1 + 6 = m + 7 by omega] using h3), (by simpa only [show m + 1 + 7 = m + 8 by omega] using h4), (by simpa only [show m + 1 + 8 = m + 9 by omega] using h5), (by simpa only [show m + 1 + 9 = m + 10 by omega] using h6), ?_⟩
        rw [show m + 1 + 10 = m + 11 by omega]
        have hr : (a (m + 11) : ℚ) = 6 * a (m + 10) - 13 * a (m + 9) + 10 * a (m + 8) + 5 * a (m + 7) - 14 * a (m + 6) + 9 * a (m + 5) - 2 * a (m + 4) := by
          have h0' := hrec (m + 11) (by omega)
          simp only [show m + 11 - 1 = m + 10 by omega, show m + 11 - 2 = m + 9 by omega, show m + 11 - 3 = m + 8 by omega, show m + 11 - 4 = m + 7 by omega, show m + 11 - 5 = m + 6 by omega, show m + 11 - 6 = m + 5 by omega, show m + 11 - 7 = m + 4 by omega] at h0'
          exact_mod_cast h0'
        rw [hr, h6, h5, h4, h3, h2, h1, h0, ← cf_rec m]
    intro n hn
    have h := (hR (n - 4)).1
    rw [show n - 4 + 4 = n by omega] at h
    exact h
  exact ⟨hrec, hgf, hcf⟩


lemma blk : ∀ p q r s : Fin 3, OMA.S_oeis_a251132.Blk p q r s ↔ okBlock p q r s := by
  simp only [OMA.S_oeis_a251132.Blk, okBlock]
  decide

lemma a_eq (m : ℕ) : OMA.S_oeis_a251132.a (m + 1) = a (m + 1) := by
  classical
  unfold OMA.S_oeis_a251132.a
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  show _ = (Finset.univ.filter (isValid (m + 1))).card
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  unfold isValid
  simp only [blk]

theorem main_proof : type_of% @OMA.S_oeis_a251132.main := by
  obtain ⟨hrec, hgf, hcf⟩ := main_proof_ours
  have hser : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (OMA.S_oeis_a251132.a n : ℚ)) =
      PowerSeries.mk (fun n => (a n : ℚ)) := by
    ext n
    cases n with
    | zero => simp [a]
    | succ m => simp [a_eq]
  have hA : ∀ n : ℕ, 1 ≤ n → OMA.S_oeis_a251132.a n = a n := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact a_eq m
  refine ⟨fun n hn => ?_, ?_, fun n hn => ?_⟩
  · rw [hA n (by omega), hA (n - 1) (by omega), hA (n - 2) (by omega), hA (n - 3) (by omega), hA (n - 4) (by omega), hA (n - 5) (by omega), hA (n - 6) (by omega), hA (n - 7) (by omega)]
    exact hrec n (by omega)
  · rw [hser, OMA.S_oeis_a251132.G, PowerSeries.eq_mul_inv_iff_mul_eq]
    · exact hgf
    · simp
  · rw [hA n (by omega)]; exact hcf n (by omega)

end OMA.P251132

theorem OMA.solution : type_of% @OMA.S_oeis_a251132.main := OMA.P251132.main_proof
