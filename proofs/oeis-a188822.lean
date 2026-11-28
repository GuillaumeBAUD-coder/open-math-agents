import OMAStatements.S_oeis_a188822

-- Credit: @Dariusthedoggie
-- Proof: row transfer matrix annihilated by the order-4 recurrence polynomial, giving recurrence, g.f. and closed forms, bridged to the Nat.card cnt encoding.

namespace OMA.P188822

open PowerSeries
/-- A `2 X 2` binary subblock `(a, b / c, d)` contains neither the diagonal pattern `0 1` (`a = 0`, `d = 1`) nor the antidiagonal pattern `0 1` (`b = 0`, `c = 1`). -/
def okBlock (a b c d : Fin 2) : Prop :=
  ¬ (a = 0 ∧ d = 1) ∧ ¬ (b = 0 ∧ c = 1)

instance (a b c d : Fin 2) : Decidable (okBlock a b c d) := by
  unfold okBlock; infer_instance

/-- An `(m + 1) X 7` `0..1` array is valid when every `2 X 2` subblock satisfies `okBlock`. -/
def isValid (m : ℕ) (x : Fin (m + 1) → Fin 7 → Fin 2) : Prop :=
  ∀ i : Fin m, ∀ j : Fin 6,
    okBlock (x i.castSucc j.castSucc) (x i.castSucc j.succ)
      (x i.succ j.castSucc) (x i.succ j.succ)

instance (m : ℕ) (x : Fin (m + 1) → Fin 7 → Fin 2) : Decidable (isValid m x) := by
  unfold isValid; infer_instance

/-- A188822: Number of n X 7 binary arrays without the pattern 0 1 diagonally or antidiagonally. -/
def a : ℕ → ℕ
  | 0 => 0
  | n + 1 => (Finset.univ.filter (isValid n)).card

abbrev Row := Fin 7 → Fin 2

def okRow (r₁ r₂ : Row) : Prop :=
  ∀ j : Fin 6, okBlock (r₁ j.castSucc) (r₁ j.succ) (r₂ j.castSucc) (r₂ j.succ)

instance (r₁ r₂ : Row) : Decidable (okRow r₁ r₂) := by
  unfold okRow; infer_instance

def enc (r : Row) : Fin 128 :=
  ⟨64 * (r 0).val + 32 * (r 1).val + 16 * (r 2).val + 8 * (r 3).val + 4 * (r 4).val + 2 * (r 5).val + (r 6).val, by
    have h0 := (r 0).isLt; have h1 := (r 1).isLt; have h2 := (r 2).isLt; have h3 := (r 3).isLt; have h4 := (r 4).isLt; have h5 := (r 5).isLt; have h6 := (r 6).isLt; omega⟩

def dec (k : Fin 128) : Row := fun c =>
  have hk := k.isLt
  if c.val = 0 then ⟨k.val / 64, by omega⟩
  else if c.val = 1 then ⟨(k.val / 32) % 2, by omega⟩
  else if c.val = 2 then ⟨(k.val / 16) % 2, by omega⟩
  else if c.val = 3 then ⟨(k.val / 8) % 2, by omega⟩
  else if c.val = 4 then ⟨(k.val / 4) % 2, by omega⟩
  else if c.val = 5 then ⟨(k.val / 2) % 2, by omega⟩
  else ⟨k.val % 2, by omega⟩

lemma enc_dec : ∀ k : Fin 128, enc (dec k) = k := by
  intro k; have hk := k.isLt; ext; simp [enc, dec]; try omega

lemma dec_enc : ∀ r : Row, dec (enc r) = r := by
  intro r; ext c
  have h0 := (r 0).isLt; have h1 := (r 1).isLt; have h2 := (r 2).isLt; have h3 := (r 3).isLt; have h4 := (r 4).isLt; have h5 := (r 5).isLt; have h6 := (r 6).isLt
  fin_cases c
  · change (dec (enc r) 0).val = (r 0).val; simp [dec, enc]; try omega
  · change (dec (enc r) 1).val = (r 1).val; simp [dec, enc]; try omega
  · change (dec (enc r) 2).val = (r 2).val; simp [dec, enc]; try omega
  · change (dec (enc r) 3).val = (r 3).val; simp [dec, enc]; try omega
  · change (dec (enc r) 4).val = (r 4).val; simp [dec, enc]; try omega
  · change (dec (enc r) 5).val = (r 5).val; simp [dec, enc]; try omega
  · change (dec (enc r) 6).val = (r 6).val; simp [dec, enc]; try omega

def ok2 (i j : Fin 128) : Prop := okRow (dec i) (dec j)

instance (i j : Fin 128) : Decidable (ok2 i j) := by
  unfold ok2; infer_instance

def adjMask (i : Fin 128) : ℕ := match i.val with
  | 0 => 1
  | 1 => 1
  | 2 => 3
  | 3 => 3
  | 4 => 1
  | 5 => 5
  | 6 => 3
  | 7 => 15
  | 8 => 1
  | 9 => 1
  | 10 => 51
  | 11 => 51
  | 12 => 1
  | 13 => 5
  | 14 => 51
  | 15 => 255
  | 16 => 1
  | 17 => 1
  | 18 => 3
  | 19 => 3
  | 20 => 257
  | 21 => 1285
  | 22 => 771
  | 23 => 3855
  | 24 => 1
  | 25 => 1
  | 26 => 51
  | 27 => 51
  | 28 => 257
  | 29 => 1285
  | 30 => 13107
  | 31 => 65535
  | 32 => 18446744073709551617
  | 33 => 18446744073709551617
  | 34 => 55340232221128654851
  | 35 => 55340232221128654851
  | 36 => 18446744073709551617
  | 37 => 92233720368547758085
  | 38 => 55340232221128654851
  | 39 => 276701161105643274255
  | 40 => 1208944266358702884323329
  | 41 => 1208944266358702884323329
  | 42 => 61656157584293847100489779
  | 43 => 61656157584293847100489779
  | 44 => 1208944266358702884323329
  | 45 => 6044721331793514421616645
  | 46 => 61656157584293847100489779
  | 47 => 308280787921469235502448895
  | 48 => 18446744073709551617
  | 49 => 18446744073709551617
  | 50 => 55340232221128654851
  | 51 => 55340232221128654851
  | 52 => 4740813226943354765569
  | 53 => 23704066134716773827845
  | 54 => 14222439680830064296707
  | 55 => 71112198404150321483535
  | 56 => 1208944266358702884323329
  | 57 => 1208944266358702884323329
  | 58 => 61656157584293847100489779
  | 59 => 61656157584293847100489779
  | 60 => 310698676454186641271095553
  | 61 => 1553493382270933206355477765
  | 62 => 15845632499163518704825873203
  | 63 => 79228162495817593524129366015
  | 64 => 1
  | 65 => 1
  | 66 => 3
  | 67 => 3
  | 68 => 1
  | 69 => 5
  | 70 => 3
  | 71 => 15
  | 72 => 1
  | 73 => 1
  | 74 => 51
  | 75 => 51
  | 76 => 1
  | 77 => 5
  | 78 => 51
  | 79 => 255
  | 80 => 4294967297
  | 81 => 4294967297
  | 82 => 12884901891
  | 83 => 12884901891
  | 84 => 1103806595329
  | 85 => 5519032976645
  | 86 => 3311419785987
  | 87 => 16557098929935
  | 88 => 4294967297
  | 89 => 4294967297
  | 90 => 219043332147
  | 91 => 219043332147
  | 92 => 1103806595329
  | 93 => 5519032976645
  | 94 => 56294136361779
  | 95 => 281470681808895
  | 96 => 18446744073709551617
  | 97 => 18446744073709551617
  | 98 => 55340232221128654851
  | 99 => 55340232221128654851
  | 100 => 18446744073709551617
  | 101 => 92233720368547758085
  | 102 => 55340232221128654851
  | 103 => 276701161105643274255
  | 104 => 1208944266358702884323329
  | 105 => 1208944266358702884323329
  | 106 => 61656157584293847100489779
  | 107 => 61656157584293847100489779
  | 108 => 1208944266358702884323329
  | 109 => 6044721331793514421616645
  | 110 => 61656157584293847100489779
  | 111 => 308280787921469235502448895
  | 112 => 79228162532711081671548469249
  | 113 => 79228162532711081671548469249
  | 114 => 237684487598133245014645407747
  | 115 => 237684487598133245014645407747
  | 116 => 20361637770906747989587956596993
  | 117 => 101808188854533739947939782984965
  | 118 => 61084913312720243968763869790979
  | 119 => 305424566563601219843819348954895
  | 120 => 5192376087906286159508272029171713
  | 121 => 5192376087906286159508272029171713
  | 122 => 264811180483220594134921873487757363
  | 123 => 264811180483220594134921873487757363
  | 124 => 1334440654591915542993625911497130241
  | 125 => 6672203272959577714968129557485651205
  | 126 => 68056473384187692692674921486353642291
  | 127 => 340282366920938463463374607431768211455
  | _ => 0

lemma ok2_iff : ∀ i j : Fin 128, ok2 i j ↔ (adjMask i / 2 ^ j.val) % 2 = 1 := by decide +kernel

def step (f : Fin 128 → ℕ) (i : Fin 128) : ℕ :=
  ∑ j : Fin 128, if ok2 i j then f j else 0

def v : ℕ → Fin 128 → ℕ
  | 0, _ => 1
  | m + 1, i => step (v m) i

lemma sum_cons {m : ℕ} (f : (Fin (m + 2) → Row) → ℕ) :
    ∑ x, f x = ∑ r : Row, ∑ y : Fin (m + 1) → Row, f (Fin.cons r y) := by
  rw [← (Fin.consEquiv (fun _ => Row)).sum_comp, Fintype.sum_prod_type]
  rfl

lemma fiber (m : ℕ) (g : (Fin (m + 1) → Row) → ℕ) :
    ∑ y, g y = ∑ i : Fin 128, ∑ y : Fin (m + 1) → Row, if enc (y 0) = i then g y else 0 := by
  trans ∑ y : Fin (m + 1) → Row, ∑ i : Fin 128, if enc (y 0) = i then g y else 0
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

lemma v_eq (m : ℕ) (i : Fin 128) :
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

lemma a_succ (n : ℕ) : a (n + 1) = ∑ i : Fin 128, v n i := by
  simp only [a, Finset.card_filter]
  rw [fiber]
  apply Finset.sum_congr rfl
  intro i _
  rw [v_eq]
  apply Finset.sum_congr rfl
  intro y _
  split_ifs <;> tauto

def vtab0 (i : Fin 128) : ℕ := match i.val with
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
  | 81 => 1
  | 82 => 1
  | 83 => 1
  | 84 => 1
  | 85 => 1
  | 86 => 1
  | 87 => 1
  | 88 => 1
  | 89 => 1
  | 90 => 1
  | 91 => 1
  | 92 => 1
  | 93 => 1
  | 94 => 1
  | 95 => 1
  | 96 => 1
  | 97 => 1
  | 98 => 1
  | 99 => 1
  | 100 => 1
  | 101 => 1
  | 102 => 1
  | 103 => 1
  | 104 => 1
  | 105 => 1
  | 106 => 1
  | 107 => 1
  | 108 => 1
  | 109 => 1
  | 110 => 1
  | 111 => 1
  | 112 => 1
  | 113 => 1
  | 114 => 1
  | 115 => 1
  | 116 => 1
  | 117 => 1
  | 118 => 1
  | 119 => 1
  | 120 => 1
  | 121 => 1
  | 122 => 1
  | 123 => 1
  | 124 => 1
  | 125 => 1
  | 126 => 1
  | 127 => 1
  | _ => 0

def vtab1 (i : Fin 128) : ℕ := match i.val with
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 1
  | 5 => 2
  | 6 => 2
  | 7 => 4
  | 8 => 1
  | 9 => 1
  | 10 => 4
  | 11 => 4
  | 12 => 1
  | 13 => 2
  | 14 => 4
  | 15 => 8
  | 16 => 1
  | 17 => 1
  | 18 => 2
  | 19 => 2
  | 20 => 2
  | 21 => 4
  | 22 => 4
  | 23 => 8
  | 24 => 1
  | 25 => 1
  | 26 => 4
  | 27 => 4
  | 28 => 2
  | 29 => 4
  | 30 => 8
  | 31 => 16
  | 32 => 2
  | 33 => 2
  | 34 => 4
  | 35 => 4
  | 36 => 2
  | 37 => 4
  | 38 => 4
  | 39 => 8
  | 40 => 4
  | 41 => 4
  | 42 => 16
  | 43 => 16
  | 44 => 4
  | 45 => 8
  | 46 => 16
  | 47 => 32
  | 48 => 2
  | 49 => 2
  | 50 => 4
  | 51 => 4
  | 52 => 4
  | 53 => 8
  | 54 => 8
  | 55 => 16
  | 56 => 4
  | 57 => 4
  | 58 => 16
  | 59 => 16
  | 60 => 8
  | 61 => 16
  | 62 => 32
  | 63 => 64
  | 64 => 1
  | 65 => 1
  | 66 => 2
  | 67 => 2
  | 68 => 1
  | 69 => 2
  | 70 => 2
  | 71 => 4
  | 72 => 1
  | 73 => 1
  | 74 => 4
  | 75 => 4
  | 76 => 1
  | 77 => 2
  | 78 => 4
  | 79 => 8
  | 80 => 2
  | 81 => 2
  | 82 => 4
  | 83 => 4
  | 84 => 4
  | 85 => 8
  | 86 => 8
  | 87 => 16
  | 88 => 2
  | 89 => 2
  | 90 => 8
  | 91 => 8
  | 92 => 4
  | 93 => 8
  | 94 => 16
  | 95 => 32
  | 96 => 2
  | 97 => 2
  | 98 => 4
  | 99 => 4
  | 100 => 2
  | 101 => 4
  | 102 => 4
  | 103 => 8
  | 104 => 4
  | 105 => 4
  | 106 => 16
  | 107 => 16
  | 108 => 4
  | 109 => 8
  | 110 => 16
  | 111 => 32
  | 112 => 4
  | 113 => 4
  | 114 => 8
  | 115 => 8
  | 116 => 8
  | 117 => 16
  | 118 => 16
  | 119 => 32
  | 120 => 8
  | 121 => 8
  | 122 => 32
  | 123 => 32
  | 124 => 16
  | 125 => 32
  | 126 => 64
  | 127 => 128
  | _ => 0

def vtab2 (i : Fin 128) : ℕ := match i.val with
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 1
  | 5 => 3
  | 6 => 2
  | 7 => 6
  | 8 => 1
  | 9 => 1
  | 10 => 5
  | 11 => 5
  | 12 => 1
  | 13 => 3
  | 14 => 5
  | 15 => 15
  | 16 => 1
  | 17 => 1
  | 18 => 2
  | 19 => 2
  | 20 => 2
  | 21 => 8
  | 22 => 4
  | 23 => 16
  | 24 => 1
  | 25 => 1
  | 26 => 5
  | 27 => 5
  | 28 => 2
  | 29 => 8
  | 30 => 10
  | 31 => 40
  | 32 => 2
  | 33 => 2
  | 34 => 4
  | 35 => 4
  | 36 => 2
  | 37 => 6
  | 38 => 4
  | 39 => 12
  | 40 => 5
  | 41 => 5
  | 42 => 34
  | 43 => 34
  | 44 => 5
  | 45 => 15
  | 46 => 34
  | 47 => 102
  | 48 => 2
  | 49 => 2
  | 50 => 4
  | 51 => 4
  | 52 => 4
  | 53 => 16
  | 54 => 8
  | 55 => 32
  | 56 => 5
  | 57 => 5
  | 58 => 34
  | 59 => 34
  | 60 => 10
  | 61 => 40
  | 62 => 68
  | 63 => 272
  | 64 => 1
  | 65 => 1
  | 66 => 2
  | 67 => 2
  | 68 => 1
  | 69 => 3
  | 70 => 2
  | 71 => 6
  | 72 => 1
  | 73 => 1
  | 74 => 5
  | 75 => 5
  | 76 => 1
  | 77 => 3
  | 78 => 5
  | 79 => 15
  | 80 => 3
  | 81 => 3
  | 82 => 6
  | 83 => 6
  | 84 => 8
  | 85 => 34
  | 86 => 16
  | 87 => 68
  | 88 => 3
  | 89 => 3
  | 90 => 15
  | 91 => 15
  | 92 => 8
  | 93 => 34
  | 94 => 40
  | 95 => 170
  | 96 => 2
  | 97 => 2
  | 98 => 4
  | 99 => 4
  | 100 => 2
  | 101 => 6
  | 102 => 4
  | 103 => 12
  | 104 => 5
  | 105 => 5
  | 106 => 34
  | 107 => 34
  | 108 => 5
  | 109 => 15
  | 110 => 34
  | 111 => 102
  | 112 => 6
  | 113 => 6
  | 114 => 12
  | 115 => 12
  | 116 => 16
  | 117 => 68
  | 118 => 32
  | 119 => 136
  | 120 => 15
  | 121 => 15
  | 122 => 102
  | 123 => 102
  | 124 => 40
  | 125 => 170
  | 126 => 272
  | 127 => 1156
  | _ => 0

def vtab3 (i : Fin 128) : ℕ := match i.val with
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 1
  | 5 => 3
  | 6 => 2
  | 7 => 6
  | 8 => 1
  | 9 => 1
  | 10 => 6
  | 11 => 6
  | 12 => 1
  | 13 => 3
  | 14 => 6
  | 15 => 18
  | 16 => 1
  | 17 => 1
  | 18 => 2
  | 19 => 2
  | 20 => 2
  | 21 => 9
  | 22 => 4
  | 23 => 18
  | 24 => 1
  | 25 => 1
  | 26 => 6
  | 27 => 6
  | 28 => 2
  | 29 => 9
  | 30 => 12
  | 31 => 54
  | 32 => 2
  | 33 => 2
  | 34 => 4
  | 35 => 4
  | 36 => 2
  | 37 => 6
  | 38 => 4
  | 39 => 12
  | 40 => 6
  | 41 => 6
  | 42 => 72
  | 43 => 72
  | 44 => 6
  | 45 => 18
  | 46 => 72
  | 47 => 216
  | 48 => 2
  | 49 => 2
  | 50 => 4
  | 51 => 4
  | 52 => 4
  | 53 => 18
  | 54 => 8
  | 55 => 36
  | 56 => 6
  | 57 => 6
  | 58 => 72
  | 59 => 72
  | 60 => 12
  | 61 => 54
  | 62 => 144
  | 63 => 648
  | 64 => 1
  | 65 => 1
  | 66 => 2
  | 67 => 2
  | 68 => 1
  | 69 => 3
  | 70 => 2
  | 71 => 6
  | 72 => 1
  | 73 => 1
  | 74 => 6
  | 75 => 6
  | 76 => 1
  | 77 => 3
  | 78 => 6
  | 79 => 18
  | 80 => 3
  | 81 => 3
  | 82 => 6
  | 83 => 6
  | 84 => 9
  | 85 => 54
  | 86 => 18
  | 87 => 108
  | 88 => 3
  | 89 => 3
  | 90 => 18
  | 91 => 18
  | 92 => 9
  | 93 => 54
  | 94 => 54
  | 95 => 324
  | 96 => 2
  | 97 => 2
  | 98 => 4
  | 99 => 4
  | 100 => 2
  | 101 => 6
  | 102 => 4
  | 103 => 12
  | 104 => 6
  | 105 => 6
  | 106 => 72
  | 107 => 72
  | 108 => 6
  | 109 => 18
  | 110 => 72
  | 111 => 216
  | 112 => 6
  | 113 => 6
  | 114 => 12
  | 115 => 12
  | 116 => 18
  | 117 => 108
  | 118 => 36
  | 119 => 216
  | 120 => 18
  | 121 => 18
  | 122 => 216
  | 123 => 216
  | 124 => 54
  | 125 => 324
  | 126 => 648
  | 127 => 3888
  | _ => 0

def vtab4 (i : Fin 128) : ℕ := match i.val with
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 1
  | 5 => 3
  | 6 => 2
  | 7 => 6
  | 8 => 1
  | 9 => 1
  | 10 => 6
  | 11 => 6
  | 12 => 1
  | 13 => 3
  | 14 => 6
  | 15 => 18
  | 16 => 1
  | 17 => 1
  | 18 => 2
  | 19 => 2
  | 20 => 2
  | 21 => 10
  | 22 => 4
  | 23 => 20
  | 24 => 1
  | 25 => 1
  | 26 => 6
  | 27 => 6
  | 28 => 2
  | 29 => 10
  | 30 => 12
  | 31 => 60
  | 32 => 2
  | 33 => 2
  | 34 => 4
  | 35 => 4
  | 36 => 2
  | 37 => 6
  | 38 => 4
  | 39 => 12
  | 40 => 6
  | 41 => 6
  | 42 => 94
  | 43 => 94
  | 44 => 6
  | 45 => 18
  | 46 => 94
  | 47 => 282
  | 48 => 2
  | 49 => 2
  | 50 => 4
  | 51 => 4
  | 52 => 4
  | 53 => 20
  | 54 => 8
  | 55 => 40
  | 56 => 6
  | 57 => 6
  | 58 => 94
  | 59 => 94
  | 60 => 12
  | 61 => 60
  | 62 => 188
  | 63 => 940
  | 64 => 1
  | 65 => 1
  | 66 => 2
  | 67 => 2
  | 68 => 1
  | 69 => 3
  | 70 => 2
  | 71 => 6
  | 72 => 1
  | 73 => 1
  | 74 => 6
  | 75 => 6
  | 76 => 1
  | 77 => 3
  | 78 => 6
  | 79 => 18
  | 80 => 3
  | 81 => 3
  | 82 => 6
  | 83 => 6
  | 84 => 10
  | 85 => 94
  | 86 => 20
  | 87 => 188
  | 88 => 3
  | 89 => 3
  | 90 => 18
  | 91 => 18
  | 92 => 10
  | 93 => 94
  | 94 => 60
  | 95 => 564
  | 96 => 2
  | 97 => 2
  | 98 => 4
  | 99 => 4
  | 100 => 2
  | 101 => 6
  | 102 => 4
  | 103 => 12
  | 104 => 6
  | 105 => 6
  | 106 => 94
  | 107 => 94
  | 108 => 6
  | 109 => 18
  | 110 => 94
  | 111 => 282
  | 112 => 6
  | 113 => 6
  | 114 => 12
  | 115 => 12
  | 116 => 20
  | 117 => 188
  | 118 => 40
  | 119 => 376
  | 120 => 18
  | 121 => 18
  | 122 => 282
  | 123 => 282
  | 124 => 60
  | 125 => 564
  | 126 => 940
  | 127 => 8836
  | _ => 0

def vtab5 (i : Fin 128) : ℕ := match i.val with
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 1
  | 5 => 3
  | 6 => 2
  | 7 => 6
  | 8 => 1
  | 9 => 1
  | 10 => 6
  | 11 => 6
  | 12 => 1
  | 13 => 3
  | 14 => 6
  | 15 => 18
  | 16 => 1
  | 17 => 1
  | 18 => 2
  | 19 => 2
  | 20 => 2
  | 21 => 10
  | 22 => 4
  | 23 => 20
  | 24 => 1
  | 25 => 1
  | 26 => 6
  | 27 => 6
  | 28 => 2
  | 29 => 10
  | 30 => 12
  | 31 => 60
  | 32 => 2
  | 33 => 2
  | 34 => 4
  | 35 => 4
  | 36 => 2
  | 37 => 6
  | 38 => 4
  | 39 => 12
  | 40 => 6
  | 41 => 6
  | 42 => 136
  | 43 => 136
  | 44 => 6
  | 45 => 18
  | 46 => 136
  | 47 => 408
  | 48 => 2
  | 49 => 2
  | 50 => 4
  | 51 => 4
  | 52 => 4
  | 53 => 20
  | 54 => 8
  | 55 => 40
  | 56 => 6
  | 57 => 6
  | 58 => 136
  | 59 => 136
  | 60 => 12
  | 61 => 60
  | 62 => 272
  | 63 => 1360
  | 64 => 1
  | 65 => 1
  | 66 => 2
  | 67 => 2
  | 68 => 1
  | 69 => 3
  | 70 => 2
  | 71 => 6
  | 72 => 1
  | 73 => 1
  | 74 => 6
  | 75 => 6
  | 76 => 1
  | 77 => 3
  | 78 => 6
  | 79 => 18
  | 80 => 3
  | 81 => 3
  | 82 => 6
  | 83 => 6
  | 84 => 10
  | 85 => 116
  | 86 => 20
  | 87 => 232
  | 88 => 3
  | 89 => 3
  | 90 => 18
  | 91 => 18
  | 92 => 10
  | 93 => 116
  | 94 => 60
  | 95 => 696
  | 96 => 2
  | 97 => 2
  | 98 => 4
  | 99 => 4
  | 100 => 2
  | 101 => 6
  | 102 => 4
  | 103 => 12
  | 104 => 6
  | 105 => 6
  | 106 => 136
  | 107 => 136
  | 108 => 6
  | 109 => 18
  | 110 => 136
  | 111 => 408
  | 112 => 6
  | 113 => 6
  | 114 => 12
  | 115 => 12
  | 116 => 20
  | 117 => 232
  | 118 => 40
  | 119 => 464
  | 120 => 18
  | 121 => 18
  | 122 => 408
  | 123 => 408
  | 124 => 60
  | 125 => 696
  | 126 => 1360
  | 127 => 15776
  | _ => 0

def vtab6 (i : Fin 128) : ℕ := match i.val with
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 1
  | 5 => 3
  | 6 => 2
  | 7 => 6
  | 8 => 1
  | 9 => 1
  | 10 => 6
  | 11 => 6
  | 12 => 1
  | 13 => 3
  | 14 => 6
  | 15 => 18
  | 16 => 1
  | 17 => 1
  | 18 => 2
  | 19 => 2
  | 20 => 2
  | 21 => 10
  | 22 => 4
  | 23 => 20
  | 24 => 1
  | 25 => 1
  | 26 => 6
  | 27 => 6
  | 28 => 2
  | 29 => 10
  | 30 => 12
  | 31 => 60
  | 32 => 2
  | 33 => 2
  | 34 => 4
  | 35 => 4
  | 36 => 2
  | 37 => 6
  | 38 => 4
  | 39 => 12
  | 40 => 6
  | 41 => 6
  | 42 => 158
  | 43 => 158
  | 44 => 6
  | 45 => 18
  | 46 => 158
  | 47 => 474
  | 48 => 2
  | 49 => 2
  | 50 => 4
  | 51 => 4
  | 52 => 4
  | 53 => 20
  | 54 => 8
  | 55 => 40
  | 56 => 6
  | 57 => 6
  | 58 => 158
  | 59 => 158
  | 60 => 12
  | 61 => 60
  | 62 => 316
  | 63 => 1580
  | 64 => 1
  | 65 => 1
  | 66 => 2
  | 67 => 2
  | 68 => 1
  | 69 => 3
  | 70 => 2
  | 71 => 6
  | 72 => 1
  | 73 => 1
  | 74 => 6
  | 75 => 6
  | 76 => 1
  | 77 => 3
  | 78 => 6
  | 79 => 18
  | 80 => 3
  | 81 => 3
  | 82 => 6
  | 83 => 6
  | 84 => 10
  | 85 => 158
  | 86 => 20
  | 87 => 316
  | 88 => 3
  | 89 => 3
  | 90 => 18
  | 91 => 18
  | 92 => 10
  | 93 => 158
  | 94 => 60
  | 95 => 948
  | 96 => 2
  | 97 => 2
  | 98 => 4
  | 99 => 4
  | 100 => 2
  | 101 => 6
  | 102 => 4
  | 103 => 12
  | 104 => 6
  | 105 => 6
  | 106 => 158
  | 107 => 158
  | 108 => 6
  | 109 => 18
  | 110 => 158
  | 111 => 474
  | 112 => 6
  | 113 => 6
  | 114 => 12
  | 115 => 12
  | 116 => 20
  | 117 => 316
  | 118 => 40
  | 119 => 632
  | 120 => 18
  | 121 => 18
  | 122 => 474
  | 123 => 474
  | 124 => 60
  | 125 => 948
  | 126 => 1580
  | 127 => 24964
  | _ => 0

def vtab7 (i : Fin 128) : ℕ := match i.val with
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 1
  | 5 => 3
  | 6 => 2
  | 7 => 6
  | 8 => 1
  | 9 => 1
  | 10 => 6
  | 11 => 6
  | 12 => 1
  | 13 => 3
  | 14 => 6
  | 15 => 18
  | 16 => 1
  | 17 => 1
  | 18 => 2
  | 19 => 2
  | 20 => 2
  | 21 => 10
  | 22 => 4
  | 23 => 20
  | 24 => 1
  | 25 => 1
  | 26 => 6
  | 27 => 6
  | 28 => 2
  | 29 => 10
  | 30 => 12
  | 31 => 60
  | 32 => 2
  | 33 => 2
  | 34 => 4
  | 35 => 4
  | 36 => 2
  | 37 => 6
  | 38 => 4
  | 39 => 12
  | 40 => 6
  | 41 => 6
  | 42 => 200
  | 43 => 200
  | 44 => 6
  | 45 => 18
  | 46 => 200
  | 47 => 600
  | 48 => 2
  | 49 => 2
  | 50 => 4
  | 51 => 4
  | 52 => 4
  | 53 => 20
  | 54 => 8
  | 55 => 40
  | 56 => 6
  | 57 => 6
  | 58 => 200
  | 59 => 200
  | 60 => 12
  | 61 => 60
  | 62 => 400
  | 63 => 2000
  | 64 => 1
  | 65 => 1
  | 66 => 2
  | 67 => 2
  | 68 => 1
  | 69 => 3
  | 70 => 2
  | 71 => 6
  | 72 => 1
  | 73 => 1
  | 74 => 6
  | 75 => 6
  | 76 => 1
  | 77 => 3
  | 78 => 6
  | 79 => 18
  | 80 => 3
  | 81 => 3
  | 82 => 6
  | 83 => 6
  | 84 => 10
  | 85 => 180
  | 86 => 20
  | 87 => 360
  | 88 => 3
  | 89 => 3
  | 90 => 18
  | 91 => 18
  | 92 => 10
  | 93 => 180
  | 94 => 60
  | 95 => 1080
  | 96 => 2
  | 97 => 2
  | 98 => 4
  | 99 => 4
  | 100 => 2
  | 101 => 6
  | 102 => 4
  | 103 => 12
  | 104 => 6
  | 105 => 6
  | 106 => 200
  | 107 => 200
  | 108 => 6
  | 109 => 18
  | 110 => 200
  | 111 => 600
  | 112 => 6
  | 113 => 6
  | 114 => 12
  | 115 => 12
  | 116 => 20
  | 117 => 360
  | 118 => 40
  | 119 => 720
  | 120 => 18
  | 121 => 18
  | 122 => 600
  | 123 => 600
  | 124 => 60
  | 125 => 1080
  | 126 => 2000
  | 127 => 36000
  | _ => 0

def vtab8 (i : Fin 128) : ℕ := match i.val with
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 1
  | 5 => 3
  | 6 => 2
  | 7 => 6
  | 8 => 1
  | 9 => 1
  | 10 => 6
  | 11 => 6
  | 12 => 1
  | 13 => 3
  | 14 => 6
  | 15 => 18
  | 16 => 1
  | 17 => 1
  | 18 => 2
  | 19 => 2
  | 20 => 2
  | 21 => 10
  | 22 => 4
  | 23 => 20
  | 24 => 1
  | 25 => 1
  | 26 => 6
  | 27 => 6
  | 28 => 2
  | 29 => 10
  | 30 => 12
  | 31 => 60
  | 32 => 2
  | 33 => 2
  | 34 => 4
  | 35 => 4
  | 36 => 2
  | 37 => 6
  | 38 => 4
  | 39 => 12
  | 40 => 6
  | 41 => 6
  | 42 => 222
  | 43 => 222
  | 44 => 6
  | 45 => 18
  | 46 => 222
  | 47 => 666
  | 48 => 2
  | 49 => 2
  | 50 => 4
  | 51 => 4
  | 52 => 4
  | 53 => 20
  | 54 => 8
  | 55 => 40
  | 56 => 6
  | 57 => 6
  | 58 => 222
  | 59 => 222
  | 60 => 12
  | 61 => 60
  | 62 => 444
  | 63 => 2220
  | 64 => 1
  | 65 => 1
  | 66 => 2
  | 67 => 2
  | 68 => 1
  | 69 => 3
  | 70 => 2
  | 71 => 6
  | 72 => 1
  | 73 => 1
  | 74 => 6
  | 75 => 6
  | 76 => 1
  | 77 => 3
  | 78 => 6
  | 79 => 18
  | 80 => 3
  | 81 => 3
  | 82 => 6
  | 83 => 6
  | 84 => 10
  | 85 => 222
  | 86 => 20
  | 87 => 444
  | 88 => 3
  | 89 => 3
  | 90 => 18
  | 91 => 18
  | 92 => 10
  | 93 => 222
  | 94 => 60
  | 95 => 1332
  | 96 => 2
  | 97 => 2
  | 98 => 4
  | 99 => 4
  | 100 => 2
  | 101 => 6
  | 102 => 4
  | 103 => 12
  | 104 => 6
  | 105 => 6
  | 106 => 222
  | 107 => 222
  | 108 => 6
  | 109 => 18
  | 110 => 222
  | 111 => 666
  | 112 => 6
  | 113 => 6
  | 114 => 12
  | 115 => 12
  | 116 => 20
  | 117 => 444
  | 118 => 40
  | 119 => 888
  | 120 => 18
  | 121 => 18
  | 122 => 666
  | 123 => 666
  | 124 => 60
  | 125 => 1332
  | 126 => 2220
  | 127 => 49284
  | _ => 0

lemma v_0 : ∀ i : Fin 128, v 0 i = vtab0 i := by decide +kernel
lemma v_1 : ∀ i : Fin 128, v 1 i = vtab1 i := by
  intro i; rw [show (1 : ℕ) = 0 + 1 from rfl, v, step]; simp only [v_0, ok2_iff]; revert i; decide +kernel
lemma v_2 : ∀ i : Fin 128, v 2 i = vtab2 i := by
  intro i; rw [show (2 : ℕ) = 1 + 1 from rfl, v, step]; simp only [v_1, ok2_iff]; revert i; decide +kernel
lemma v_3 : ∀ i : Fin 128, v 3 i = vtab3 i := by
  intro i; rw [show (3 : ℕ) = 2 + 1 from rfl, v, step]; simp only [v_2, ok2_iff]; revert i; decide +kernel
lemma v_4 : ∀ i : Fin 128, v 4 i = vtab4 i := by
  intro i; rw [show (4 : ℕ) = 3 + 1 from rfl, v, step]; simp only [v_3, ok2_iff]; revert i; decide +kernel
lemma v_5 : ∀ i : Fin 128, v 5 i = vtab5 i := by
  intro i; rw [show (5 : ℕ) = 4 + 1 from rfl, v, step]; simp only [v_4, ok2_iff]; revert i; decide +kernel
lemma v_6 : ∀ i : Fin 128, v 6 i = vtab6 i := by
  intro i; rw [show (6 : ℕ) = 5 + 1 from rfl, v, step]; simp only [v_5, ok2_iff]; revert i; decide +kernel
lemma v_7 : ∀ i : Fin 128, v 7 i = vtab7 i := by
  intro i; rw [show (7 : ℕ) = 6 + 1 from rfl, v, step]; simp only [v_6, ok2_iff]; revert i; decide +kernel
lemma v_8 : ∀ i : Fin 128, v 8 i = vtab8 i := by
  intro i; rw [show (8 : ℕ) = 7 + 1 from rfl, v, step]; simp only [v_7, ok2_iff]; revert i; decide +kernel

def err (m : ℕ) (i : Fin 128) : ℤ :=
  (v (m + 4) i : ℤ) - 2 * (v (m + 3) i : ℤ) + 2 * (v (m + 1) i : ℤ) - (v m i : ℤ)

lemma err_base : ∀ i : Fin 128, err 4 i = 0 := by
  intro i
  change (v 8 i : ℤ) - 2 * (v 7 i : ℤ) + 2 * (v 5 i : ℤ) - (v 4 i : ℤ) = 0
  simp only [v_8, v_7, v_5, v_4]
  revert i; decide +kernel

lemma err_succ (m : ℕ) (i : Fin 128) :
    err (m + 1) i = ∑ j : Fin 128, if ok2 i j then err m j else 0 := by
  have hV : ∀ r, (v (r + 1) i : ℤ) = ∑ j : Fin 128, if ok2 i j then (v r j : ℤ) else 0 := by
    intro r; rw [v, step]; simp only [Nat.cast_sum, apply_ite Nat.cast, Nat.cast_zero]
  unfold err
  simp only [hV]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> ring

lemma err_ge (m : ℕ) (i : Fin 128) : err (m + 4) i = 0 := by
  induction m generalizing i with
  | zero => simpa using err_base i
  | succ m ih =>
    rw [show m + 1 + 4 = (m + 4) + 1 by omega, err_succ]
    exact Finset.sum_eq_zero (fun j _ => by simp [ih j])

lemma a_rec_ge (m : ℕ) :
    (a (m + 9) : ℤ) = 2 * a (m + 8) - 2 * a (m + 6) + a (m + 5) := by
  have h : ∑ i : Fin 128, err (m + 4) i = 0 :=
    Finset.sum_eq_zero (fun i _ => err_ge m i)
  unfold err at h
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at h
  have hsum : ∀ r : ℕ, (∑ i : Fin 128, (v (m + 4 + r) i : ℤ)) = (a (m + 4 + r + 1) : ℤ) := by
    intro r
    rw [a_succ, Nat.cast_sum]
  have hsum0 : (∑ i : Fin 128, (v (m + 4) i : ℤ)) = (a (m + 4 + 1) : ℤ) := by
    rw [a_succ, Nat.cast_sum]
  simp only [hsum, hsum0] at h
  have h2_0 : m + 4 + 1 = m + 5 := by omega
  have h2_1 : m + 4 + 1 + 1 = m + 6 := by omega
  have h2_3 : m + 4 + 3 + 1 = m + 8 := by omega
  have h2_4 : m + 4 + 4 + 1 = m + 9 := by omega
  simp only [h2_0, h2_1, h2_3, h2_4] at h
  linarith


lemma a_0 : a 0 = 0 := rfl
lemma a_1 : a 1 = 128 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, a_succ]
  change ∑ i : Fin 128, v 0 i = 128
  simp only [v_0]; decide +kernel
lemma a_2 : a 2 = 1156 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, a_succ]
  change ∑ i : Fin 128, v 1 i = 1156
  simp only [v_1]; decide +kernel
lemma a_3 : a 3 = 3888 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, a_succ]
  change ∑ i : Fin 128, v 2 i = 3888
  simp only [v_2]; decide +kernel
lemma a_4 : a 4 = 8836 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, a_succ]
  change ∑ i : Fin 128, v 3 i = 8836
  simp only [v_3]; decide +kernel
lemma a_5 : a 5 = 15776 := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, a_succ]
  change ∑ i : Fin 128, v 4 i = 15776
  simp only [v_4]; decide +kernel
lemma a_6 : a 6 = 24964 := by
  rw [show (6 : ℕ) = 5 + 1 from rfl, a_succ]
  change ∑ i : Fin 128, v 5 i = 24964
  simp only [v_5]; decide +kernel
lemma a_7 : a 7 = 36000 := by
  rw [show (7 : ℕ) = 6 + 1 from rfl, a_succ]
  change ∑ i : Fin 128, v 6 i = 36000
  simp only [v_6]; decide +kernel
lemma a_8 : a 8 = 49284 := by
  rw [show (8 : ℕ) = 7 + 1 from rfl, a_succ]
  change ∑ i : Fin 128, v 7 i = 49284
  simp only [v_7]; decide +kernel

def cfC (n : ℕ) : ℚ :=
  ((2 * (578 - 1088 * (n : ℚ) + 512 * (n : ℚ) ^ 2)) * (1 + (-1 : ℚ) ^ n) + (2 * (528 - 1088 * (n : ℚ) + 512 * (n : ℚ) ^ 2)) * (1 - (-1 : ℚ) ^ n)) / 2


theorem main_proof_ours :
    (∀ n : ℕ, 8 ≤ n → (a n : ℤ) = 2 * a (n - 1) - 2 * a (n - 3) + a (n - 4)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 3 * (1 + X)) =
      4 * X * (32 + 225 * X + 394 * X ^ 2 + 329 * X ^ 3 + 72 * X ^ 4 + 8 * X ^ 5 - 36 * X ^ 6)) ∧
    (∀ n : ℕ, 4 ≤ n → Even n → (a n : ℚ) = 2 * (578 - 1088 * (n : ℚ) + 512 * (n : ℚ) ^ 2)) ∧
    (∀ n : ℕ, 4 ≤ n → Odd n → (a n : ℚ) = 2 * (528 - 1088 * (n : ℚ) + 512 * (n : ℚ) ^ 2)) := by
  have hrec : ∀ n : ℕ, 8 ≤ n → (a n : ℤ) = 2 * a (n - 1) - 2 * a (n - 3) + a (n - 4) := by
    intro n hn
    rcases Nat.lt_or_ge n 9 with hlt | hge
    · interval_cases n <;> simp [a_0, a_1, a_2, a_3, a_4, a_5, a_6, a_7, a_8]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
      simpa using a_rec_ge m
  have hgf : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 3 * (1 + X)) =
      4 * X * (32 + 225 * X + 394 * X ^ 2 + 329 * X ^ 3 + 72 * X ^ 4 + 8 * X ^ 5 - 36 * X ^ 6) := by
    have hl : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 3 * (1 + X)) =
        PowerSeries.mk (fun n => (a n : ℚ))
        - C (2 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 1)
        + C (2 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 3)
        - C (1 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 4) := by
      simp only [map_ofNat, map_one]; ring
    have hr : (4 * X * (32 + 225 * X + 394 * X ^ 2 + 329 * X ^ 3 + 72 * X ^ 4 + 8 * X ^ 5 - 36 * X ^ 6) : PowerSeries ℚ) =
        C (128 : ℚ) * X ^ 1 + C (900 : ℚ) * X ^ 2 + C (1576 : ℚ) * X ^ 3 + C (1316 : ℚ) * X ^ 4 + C (288 : ℚ) * X ^ 5 + C (32 : ℚ) * X ^ 6 - C (144 : ℚ) * X ^ 7 := by
      simp only [map_ofNat, map_one]; ring
    rw [hl, hr]
    ext n
    simp only [map_sub, map_add, map_neg, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
    rcases Nat.lt_or_ge n 8 with hn | hn
    · interval_cases n <;> simp [a_0, a_1, a_2, a_3, a_4, a_5, a_6, a_7, a_8] <;> try norm_num
    · have hq : (a n : ℚ) = 2 * a (n - 1) - 2 * a (n - 3) + a (n - 4) := by
        exact_mod_cast hrec n (by omega)
      have c1 : 1 ≤ n := by omega
      have c3 : 3 ≤ n := by omega
      have c4 : 4 ≤ n := by omega
      have e1 : n - 1 ≠ 0 := by omega
      have e2 : n - 2 ≠ 0 := by omega
      have e3 : n - 3 ≠ 0 := by omega
      have e4 : n - 4 ≠ 0 := by omega
      have e5 : n - 5 ≠ 0 := by omega
      have e6 : n - 6 ≠ 0 := by omega
      have e7 : n - 7 ≠ 0 := by omega
      simp only [c1, c3, c4, e1, e2, e3, e4, e5, e6, e7, coeff_C, if_true, if_false, ite_self]
      rw [hq]; ring
  have hcfC : ∀ n : ℕ, 4 ≤ n → (a n : ℚ) = ((2 * (578 - 1088 * (n : ℚ) + 512 * (n : ℚ) ^ 2)) * (1 + (-1 : ℚ) ^ n) + (2 * (528 - 1088 * (n : ℚ) + 512 * (n : ℚ) ^ 2)) * (1 - (-1 : ℚ) ^ n)) / 2 := by
    have hb_4 : (a 4 : ℚ) = cfC 4 := by
      rw [a_4]; unfold cfC
      push_cast
      norm_num
    have hb_5 : (a 5 : ℚ) = cfC 5 := by
      rw [a_5]; unfold cfC
      push_cast
      norm_num
    have hb_6 : (a 6 : ℚ) = cfC 6 := by
      rw [a_6]; unfold cfC
      push_cast
      norm_num
    have hb_7 : (a 7 : ℚ) = cfC 7 := by
      rw [a_7]; unfold cfC
      push_cast
      norm_num
    have cf_rec : ∀ m : ℕ, cfC (m + 8) = 2 * cfC (m + 7) - 2 * cfC (m + 5) + cfC (m + 4) := by
      intro m
      unfold cfC
      have hp_sg_1 : (-1 : ℚ) ^ (m + 5) = (-1 : ℚ) ^ (m + 4) * (-1 : ℚ) ^ 1 := by
        rw [show m + 5 = (m + 4) + 1 by omega, pow_add]
      have hp_sg_2 : (-1 : ℚ) ^ (m + 6) = (-1 : ℚ) ^ (m + 4) * (-1 : ℚ) ^ 2 := by
        rw [show m + 6 = (m + 4) + 2 by omega, pow_add]
      have hp_sg_3 : (-1 : ℚ) ^ (m + 7) = (-1 : ℚ) ^ (m + 4) * (-1 : ℚ) ^ 3 := by
        rw [show m + 7 = (m + 4) + 3 by omega, pow_add]
      have hp_sg_4 : (-1 : ℚ) ^ (m + 8) = (-1 : ℚ) ^ (m + 4) * (-1 : ℚ) ^ 4 := by
        rw [show m + 8 = (m + 4) + 4 by omega, pow_add]
      simp only [hp_sg_1, hp_sg_2, hp_sg_3, hp_sg_4]
      generalize (-1 : ℚ) ^ (m + 4) = Xsg
      push_cast
      ring
    have hR : ∀ m : ℕ,
        (a (m + 4) : ℚ) = cfC (m + 4) ∧
        (a (m + 5) : ℚ) = cfC (m + 5) ∧
        (a (m + 6) : ℚ) = cfC (m + 6) ∧
        (a (m + 7) : ℚ) = cfC (m + 7) := by
      intro m
      induction m with
      | zero =>
        simp only [Nat.zero_add]
        exact ⟨hb_4, hb_5, hb_6, hb_7⟩
      | succ m ih =>
        obtain ⟨h0, h1, h2, h3⟩ := ih
        refine ⟨(by simpa only [show m + 1 + 4 = m + 5 by omega] using h1), (by simpa only [show m + 1 + 5 = m + 6 by omega] using h2), (by simpa only [show m + 1 + 6 = m + 7 by omega] using h3), ?_⟩
        rw [show m + 1 + 7 = m + 8 by omega]
        have hr : (a (m + 8) : ℚ) = 2 * a (m + 7) - 2 * a (m + 5) + a (m + 4) := by
          have h0' := hrec (m + 8) (by omega)
          simp only [show m + 8 - 1 = m + 7 by omega, show m + 8 - 3 = m + 5 by omega, show m + 8 - 4 = m + 4 by omega] at h0'
          exact_mod_cast h0'
        rw [hr, h3, h1, h0, ← cf_rec m]
    intro n hn
    have h := (hR (n - 4)).1
    rw [show n - 4 + 4 = n by omega] at h
    exact h
  have hcfE : ∀ n : ℕ, 4 ≤ n → Even n → (a n : ℚ) = 2 * (578 - 1088 * (n : ℚ) + 512 * (n : ℚ) ^ 2) := by
    intro n hn he
    rw [hcfC n hn, he.neg_one_pow]
    ring
  have hcfO : ∀ n : ℕ, 4 ≤ n → Odd n → (a n : ℚ) = 2 * (528 - 1088 * (n : ℚ) + 512 * (n : ℚ) ^ 2) := by
    intro n hn ho
    rw [hcfC n hn, ho.neg_one_pow]
    ring
  exact ⟨hrec, hgf, hcfE, hcfO⟩


lemma a_eq (m : ℕ) : OMA.S_oeis_a188822.a (m + 1) = a (m + 1) := by
  classical
  unfold OMA.S_oeis_a188822.a OMA.S_oeis_a188822.cnt
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  show _ = (Finset.univ.filter (isValid m)).card
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  unfold isValid okBlock OMA.S_oeis_a188822.PairOK
  exact Iff.rfl

theorem main_proof : type_of% @OMA.S_oeis_a188822.main := by
  obtain ⟨hrec, hgf, hev, hod⟩ := main_proof_ours
  have hser : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (OMA.S_oeis_a188822.a n : ℚ)) =
      PowerSeries.mk (fun n => (a n : ℚ)) := by
    ext n
    cases n with
    | zero => simp [a]
    | succ m => simp [a_eq]
  have hA : ∀ n : ℕ, 1 ≤ n → OMA.S_oeis_a188822.a n = a n := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact a_eq m
  refine ⟨fun n hn => ?_, ?_, fun n hn h2 => ?_, fun n hn h2 => ?_⟩
  · rw [hA n (by omega), hA (n - 1) (by omega), hA (n - 3) (by omega), hA (n - 4) (by omega)]
    have := hrec n hn
    omega
  · rw [hser, OMA.S_oeis_a188822.G, PowerSeries.eq_mul_inv_iff_mul_eq]
    · rw [hgf]; ring
    · simp
  · rw [hA n (by omega)]; exact hev n hn h2
  · rw [hA n (by omega)]; exact hod n hn h2

end OMA.P188822

theorem OMA.solution : type_of% @OMA.S_oeis_a188822.main := OMA.P188822.main_proof
