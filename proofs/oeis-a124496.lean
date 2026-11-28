import OMAStatements.S_oeis_a124496

-- Problem: A124496: Triangle read by rows: T(n,k) is the number of set partitions of {1,2,...,n} in which the size of the last block is k, 1<=k<=n; the blocks are ordered with increasing least elements
-- Upstream: statements/oeis-a124496.lean (declaration OMA.S_oeis_a124496.main)
-- Credit: @timlantin (the owner of the agent is credited as the solver)
--
-- Proof sketch. For a restricted growth function s of length n let M be its maximum and d(s) the
-- number of positions where the value is not M, so that T(n,k) counts the s with d(s) = n - k.
-- Appending a letter v in 1..M+1 to s: v < M gives (M, d+1) (M-1 ways), v = M gives (M, d) and
-- v = M+1 gives (M+1, n). For a weight w on the maxima put S(n,e,w) = sum of w(max s) over the s
-- of length n with d(s) = e. Then, for n >= 1,
--   S(n+1,e+1,w) = S(n,e,(M-1)w) + S(n,e+1,w) + [e+1 = n] sum_t w(max t + 1),
-- and S(n+1,0,w) = S(n,0,w). By induction on n, for every w:
--   S(n,0,w) = w(1) (n >= 1),  S(n,1,w) = w(2) (n >= 2),  S(n,2,w) = (n-1) w(2) + w(3) (n >= 3),
--   2 S(n,3,w) = (n-1)(n-2) w(2) + (4n-6) w(3) + 2 w(4) (n >= 4),
--   6 S(n,4,1) = (n-2)(n^2+8n-3) (n >= 5).
-- With w = 1 the fourth line is 2 T(n,n-3) = (n-1)(n+2) and the fifth is the second claim.

namespace OMA.P124496
open OMA.S_oeis_a124496

/-- The transfer operator on functions of the maximum. -/
def Tr (f : ℕ → ℕ) : ℕ → ℕ := fun m => m * f m + f (m + 1)

/-- The restricted growth strings of length `n`, built letter by letter. -/
def R : (n : ℕ) → Finset (Fin n → ℕ)
  | 0 => {fun _ => 0}
  | n + 1 => ((R n).sigma fun s => Finset.Icc 1 (Finset.univ.sup s + 1)).image
      fun p => (Fin.snoc p.1 p.2 : Fin (n + 1) → ℕ)

lemma sc {n : ℕ} (t : Fin n → ℕ) (v : ℕ) (i : Fin n) :
    (Fin.snoc t v : Fin (n + 1) → ℕ) i.castSucc = t i := by simp

lemma sl {n : ℕ} (t : Fin n → ℕ) (v : ℕ) :
    (Fin.snoc t v : Fin (n + 1) → ℕ) (Fin.last n) = v := by simp

lemma sup_snoc {n : ℕ} (t : Fin n → ℕ) (v : ℕ) :
    Finset.univ.sup (Fin.snoc t v : Fin (n + 1) → ℕ) = max (Finset.univ.sup t) v := by
  apply le_antisymm
  · apply Finset.sup_le
    intro j _
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [sl]
      exact le_max_right _ _
    · rw [sc]
      exact le_trans (Finset.le_sup (f := t) (Finset.mem_univ i)) (le_max_left _ _)
  · apply max_le
    · apply Finset.sup_le
      intro i _
      have h := Finset.le_sup (f := (Fin.snoc t v : Fin (n + 1) → ℕ))
        (Finset.mem_univ i.castSucc)
      rwa [sc] at h
    · have h := Finset.le_sup (f := (Fin.snoc t v : Fin (n + 1) → ℕ))
        (Finset.mem_univ (Fin.last n))
      rwa [sl] at h

lemma sup_Iio_castSucc {n : ℕ} (t : Fin n → ℕ) (v : ℕ) (i : Fin n) :
    (Finset.Iio i.castSucc).sup (Fin.snoc t v : Fin (n + 1) → ℕ) = (Finset.Iio i).sup t := by
  apply le_antisymm
  · apply Finset.sup_le
    intro j hj
    have h0 : j < i.castSucc := Finset.mem_Iio.mp hj
    have h1 : (j : ℕ) < (i : ℕ) := h0
    have h2 := i.isLt
    have hj' : j = (⟨j, by omega⟩ : Fin n).castSucc := Fin.ext rfl
    rw [hj', sc]
    exact Finset.le_sup (f := t) (Finset.mem_Iio.mpr (Fin.lt_def.mpr h1))
  · apply Finset.sup_le
    intro j hj
    have h1 : j < i := Finset.mem_Iio.mp hj
    have h := Finset.le_sup (f := (Fin.snoc t v : Fin (n + 1) → ℕ))
      (show j.castSucc ∈ Finset.Iio i.castSucc from
        Finset.mem_Iio.mpr (Fin.castSucc_lt_castSucc_iff.mpr h1))
    rwa [sc] at h

lemma sup_Iio_last {n : ℕ} (t : Fin n → ℕ) (v : ℕ) :
    (Finset.Iio (Fin.last n)).sup (Fin.snoc t v : Fin (n + 1) → ℕ) = Finset.univ.sup t := by
  apply le_antisymm
  · apply Finset.sup_le
    intro j hj
    have h0 : j < Fin.last n := Finset.mem_Iio.mp hj
    have h1 : (j : ℕ) < n := h0
    have hj' : j = (⟨j, h1⟩ : Fin n).castSucc := Fin.ext rfl
    rw [hj', sc]
    exact Finset.le_sup (f := t) (Finset.mem_univ _)
  · apply Finset.sup_le
    intro j _
    have h := Finset.le_sup (f := (Fin.snoc t v : Fin (n + 1) → ℕ))
      (show j.castSucc ∈ Finset.Iio (Fin.last n) from Finset.mem_Iio.mpr (Fin.castSucc_lt_last j))
    rwa [sc] at h

lemma isRGF_snoc {n : ℕ} (t : Fin n → ℕ) (v : ℕ) :
    IsRGF (Fin.snoc t v : Fin (n + 1) → ℕ) ↔
      IsRGF t ∧ v ∈ Finset.Icc 1 (Finset.univ.sup t + 1) := by
  unfold IsRGF
  rw [Fin.forall_fin_succ']
  simp only [sc, sl, sup_Iio_castSucc, sup_Iio_last, Finset.mem_Icc]
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  omega

lemma mem_R : ∀ (n : ℕ) (s : Fin n → ℕ), s ∈ R n ↔ IsRGF s := by
  intro n
  induction n with
  | zero =>
    intro s
    rw [R, Finset.mem_singleton]
    constructor
    · intro _ i
      exact i.elim0
    · intro _
      funext i
      exact i.elim0
  | succ n ih =>
    intro s
    have e : (Fin.snoc (Fin.init s) (s (Fin.last n)) : Fin (n + 1) → ℕ) = s :=
      Fin.snoc_init_self s
    rw [R, Finset.mem_image]
    constructor
    · rintro ⟨p, hp, rfl⟩
      rw [Finset.mem_sigma] at hp
      exact (isRGF_snoc _ _).mpr ⟨(ih _).mp hp.1, hp.2⟩
    · intro h
      have h' := (isRGF_snoc (Fin.init s) (s (Fin.last n))).mp (by rw [e]; exact h)
      exact ⟨⟨Fin.init s, s (Fin.last n)⟩,
        Finset.mem_sigma.mpr ⟨(ih _).mpr h'.1, h'.2⟩, e⟩

lemma sum_R_succ (n : ℕ) (g : (Fin (n + 1) → ℕ) → ℕ) :
    ∑ s ∈ R (n + 1), g s =
      ∑ t ∈ R n, ∑ v ∈ Finset.Icc 1 (Finset.univ.sup t + 1), g (Fin.snoc t v) := by
  rw [R, Finset.sum_image, Finset.sum_sigma]
  rintro ⟨a, b⟩ _ ⟨c, d⟩ _ h
  have h0 : (Fin.snoc a b : Fin (n + 1) → ℕ) = Fin.snoc c d := h
  have h1 : a = c := by
    funext i
    have h3 := congrFun h0 i.castSucc
    rwa [sc, sc] at h3
  have h2 : b = d := by
    have h3 := congrFun h0 (Fin.last n)
    rwa [sl, sl] at h3
  subst h1
  subst h2
  rfl

lemma sum_sup_step (M : ℕ) (f : ℕ → ℕ) :
    ∑ v ∈ Finset.Icc 1 (M + 1), f (max M v) = Tr f M := by
  have h : ∑ v ∈ Finset.Icc 1 M, f (max M v) = ∑ v ∈ Finset.Icc 1 M, f M :=
    Finset.sum_congr rfl fun v hv => by rw [max_eq_left (Finset.mem_Icc.mp hv).2]
  rw [Finset.sum_Icc_succ_top (by omega), h, Finset.sum_const, Nat.card_Icc,
    max_eq_right (Nat.le_succ M)]
  show _ = M * f M + f (M + 1)
  simp

lemma Q (n : ℕ) : ∀ h : ℕ → ℕ, ∑ s ∈ R n, h (Finset.univ.sup s) = Tr^[n] h 0 := by
  induction n with
  | zero =>
    intro h
    simp [R]
  | succ n ih =>
    intro h
    rw [sum_R_succ, Function.iterate_succ_apply, ← ih]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [sup_snoc]
    exact sum_sup_step _ _

lemma one_le_sup (m : ℕ) (t : Fin (m + 1) → ℕ) (ht : t ∈ R (m + 1)) :
    1 ≤ Finset.univ.sup t :=
  le_trans ((mem_R _ t).mp ht 0).1 (Finset.le_sup (f := t) (Finset.mem_univ 0))

/-- The number of positions where the value is not the maximum. -/
def df {n : ℕ} (s : Fin n → ℕ) : ℕ := ∑ i, if s i = Finset.univ.sup s then 0 else 1

lemma df_lt {n : ℕ} (t : Fin n → ℕ) (v : ℕ) (hv : v < Finset.univ.sup t) :
    df (Fin.snoc t v : Fin (n + 1) → ℕ) = df t + 1 := by
  unfold df
  rw [Fin.sum_univ_castSucc]
  simp only [sc, sl, sup_snoc, max_eq_left hv.le]
  rw [if_neg hv.ne]

lemma df_eq {n : ℕ} (t : Fin n → ℕ) :
    df (Fin.snoc t (Finset.univ.sup t) : Fin (n + 1) → ℕ) = df t := by
  unfold df
  rw [Fin.sum_univ_castSucc]
  simp only [sc, sl, sup_snoc, max_self]
  simp

lemma df_new {n : ℕ} (t : Fin n → ℕ) :
    df (Fin.snoc t (Finset.univ.sup t + 1) : Fin (n + 1) → ℕ) = n := by
  unfold df
  rw [Fin.sum_univ_castSucc]
  simp only [sc, sl, sup_snoc, max_eq_right (Nat.le_succ _)]
  have h : ∀ i : Fin n, (if t i = Finset.univ.sup t + 1 then 0 else 1) = 1 := fun i =>
    if_neg (by have h2 := Finset.le_sup (f := t) (Finset.mem_univ i); omega)
  simp [h]

lemma per_t {n : ℕ} (t : Fin n → ℕ) (K : ℕ) (hK : Finset.univ.sup t = K + 1)
    (g : ℕ → ℕ → ℕ) :
    ∑ v ∈ Finset.Icc 1 (Finset.univ.sup t + 1),
        g (Finset.univ.sup (Fin.snoc t v : Fin (n + 1) → ℕ))
          (df (Fin.snoc t v : Fin (n + 1) → ℕ)) =
      K * g (K + 1) (df t + 1) + g (K + 1) (df t) + g (K + 2) n := by
  have h1 : ∀ v ∈ Finset.Icc 1 K,
      g (Finset.univ.sup (Fin.snoc t v : Fin (n + 1) → ℕ))
        (df (Fin.snoc t v : Fin (n + 1) → ℕ)) = g (K + 1) (df t + 1) := by
    intro v hv
    have h4 := (Finset.mem_Icc.mp hv).2
    rw [df_lt t v (by omega), sup_snoc, hK, max_eq_left (by omega)]
  have h2 : g (Finset.univ.sup (Fin.snoc t (K + 1) : Fin (n + 1) → ℕ))
      (df (Fin.snoc t (K + 1) : Fin (n + 1) → ℕ)) = g (K + 1) (df t) := by
    have h4 := df_eq t
    rw [hK] at h4
    rw [h4, sup_snoc, hK, max_self]
  have h3 : g (Finset.univ.sup (Fin.snoc t (K + 1 + 1) : Fin (n + 1) → ℕ))
      (df (Fin.snoc t (K + 1 + 1) : Fin (n + 1) → ℕ)) = g (K + 2) n := by
    have h4 := df_new t
    rw [hK] at h4
    rw [h4, sup_snoc, hK, max_eq_right (Nat.le_succ _)]
  rw [hK, Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega),
    Finset.sum_congr rfl h1, h2, h3, Finset.sum_const, Nat.card_Icc]
  simp

lemma GEN (m : ℕ) (g : ℕ → ℕ → ℕ) :
    ∑ s ∈ R (m + 2), g (Finset.univ.sup s) (df s) =
      ∑ t ∈ R (m + 1), ((Finset.univ.sup t - 1) * g (Finset.univ.sup t) (df t + 1) +
        g (Finset.univ.sup t) (df t) + g (Finset.univ.sup t + 1) (m + 1)) := by
  show ∑ s ∈ R (m + 1 + 1), g (Finset.univ.sup s) (df s) = _
  rw [sum_R_succ]
  refine Finset.sum_congr rfl fun t ht => ?_
  obtain ⟨K, hK⟩ : ∃ K, Finset.univ.sup t = K + 1 :=
    ⟨Finset.univ.sup t - 1, by have h := one_le_sup m t ht; omega⟩
  rw [per_t t K hK g, hK, Nat.add_sub_cancel]

lemma GEN0 (g : ℕ → ℕ → ℕ) : ∑ s ∈ R 1, g (Finset.univ.sup s) (df s) = g 1 0 := by
  show ∑ s ∈ R (0 + 1), g (Finset.univ.sup s) (df s) = _
  rw [sum_R_succ]
  have hs : Finset.univ.sup (fun _ : Fin 0 => (0 : ℕ)) = 0 := by simp
  have h3 := df_new (fun _ : Fin 0 => (0 : ℕ))
  rw [hs] at h3
  simp only [zero_add] at h3
  rw [R, Finset.sum_singleton, hs]
  simp only [zero_add, Finset.Icc_self, Finset.sum_singleton]
  rw [h3, sup_snoc, hs]
  simp

/-- Sum of `w (max s)` over the functions of length `n` with `df s = e`. -/
def Sd (n e : ℕ) (w : ℕ → ℕ) : ℕ :=
  ∑ s ∈ R n, if df s = e then w (Finset.univ.sup s) else 0

lemma step_succ (m e : ℕ) (w : ℕ → ℕ) :
    Sd (m + 2) (e + 1) w = Sd (m + 1) e (fun M => (M - 1) * w M) + Sd (m + 1) (e + 1) w +
      (if e = m then ∑ t ∈ R (m + 1), w (Finset.univ.sup t + 1) else 0) := by
  unfold Sd
  refine (GEN m (fun M d => if d = e + 1 then w M else 0)).trans ?_
  simp only [Finset.sum_add_distrib]
  congr 1
  · congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases h : df t = e <;> simp [h]
  · by_cases h : e = m
    · subst h
      simp
    · have h' : ¬ (m = e) := by omega
      simp [h, h']

lemma step_zero (m : ℕ) (w : ℕ → ℕ) : Sd (m + 2) 0 w = Sd (m + 1) 0 w := by
  unfold Sd
  refine (GEN m (fun M d => if d = 0 then w M else 0)).trans ?_
  refine Finset.sum_congr rfl fun t _ => ?_
  simp

lemma Z (m : ℕ) : ∀ (e : ℕ) (w : ℕ → ℕ), m < e → Sd (m + 1) e w = 0 := by
  induction m with
  | zero =>
    intro e w h
    exact (GEN0 (fun M d => if d = e then w M else 0)).trans (if_neg (by omega))
  | succ m ih =>
    intro e w h
    obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    show Sd (m + 2) (e' + 1) w = 0
    rw [step_succ, ih e' _ (by omega), ih (e' + 1) _ (by omega), if_neg (by omega)]

lemma C0 (m : ℕ) : ∀ w : ℕ → ℕ, Sd (m + 1) 0 w = w 1 := by
  induction m with
  | zero =>
    intro w
    exact (GEN0 (fun M d => if d = 0 then w M else 0)).trans (if_pos rfl)
  | succ m ih =>
    intro w
    show Sd (m + 2) 0 w = w 1
    rw [step_zero, ih]

lemma C1 (m : ℕ) : ∀ w : ℕ → ℕ, Sd (m + 2) 1 w = w 2 := by
  induction m with
  | zero =>
    intro w
    have h : Sd 2 1 w = Sd 1 0 (fun M => (M - 1) * w M) + Sd 1 1 w +
        (if 0 = 0 then ∑ t ∈ R 1, w (Finset.univ.sup t + 1) else 0) := step_succ 0 0 w
    have q : ∑ t ∈ R 1, w (Finset.univ.sup t + 1) = w 2 := GEN0 (fun M _ => w (M + 1))
    show Sd 2 1 w = w 2
    rw [h, C0 0, Z 0 1 w (by omega), if_pos rfl, q]
    simp
  | succ m ih =>
    intro w
    have h : Sd (m + 1 + 2) 1 w = Sd (m + 2) 0 (fun M => (M - 1) * w M) + Sd (m + 2) 1 w +
        (if 0 = m + 1 then ∑ t ∈ R (m + 2), w (Finset.univ.sup t + 1) else 0) :=
      step_succ (m + 1) 0 w
    rw [h, C0 (m + 1), ih, if_neg (by omega)]
    simp

lemma C2 (m : ℕ) : ∀ w : ℕ → ℕ, Sd (m + 3) 2 w = (m + 2) * w 2 + w 3 := by
  induction m with
  | zero =>
    intro w
    have h : Sd 3 2 w = Sd 2 1 (fun M => (M - 1) * w M) + Sd 2 2 w +
        (if 1 = 1 then ∑ t ∈ R 2, w (Finset.univ.sup t + 1) else 0) := step_succ 1 1 w
    have q : ∑ t ∈ R 2, w (Finset.univ.sup t + 1) = w 2 + w 3 := by
      refine (Q 2 (fun M => w (M + 1))).trans ?_
      show Tr (Tr (fun M => w (M + 1))) 0 = _
      simp [Tr]
    show Sd 3 2 w = (0 + 2) * w 2 + w 3
    rw [h, C1 0, Z 1 2 w (by omega), if_pos rfl, q]
    simp
    ring
  | succ m ih =>
    intro w
    have h : Sd (m + 1 + 3) 2 w = Sd (m + 3) 1 (fun M => (M - 1) * w M) + Sd (m + 3) 2 w +
        (if 1 = m + 2 then ∑ t ∈ R (m + 3), w (Finset.univ.sup t + 1) else 0) :=
      step_succ (m + 2) 1 w
    rw [h, C1 (m + 1), ih, if_neg (by omega)]
    simp
    ring

lemma C3 (m : ℕ) : ∀ w : ℕ → ℕ,
    2 * Sd (m + 4) 3 w = (m + 3) * (m + 2) * w 2 + (4 * m + 10) * w 3 + 2 * w 4 := by
  induction m with
  | zero =>
    intro w
    have h : Sd 4 3 w = Sd 3 2 (fun M => (M - 1) * w M) + Sd 3 3 w +
        (if 2 = 2 then ∑ t ∈ R 3, w (Finset.univ.sup t + 1) else 0) := step_succ 2 2 w
    have q : ∑ t ∈ R 3, w (Finset.univ.sup t + 1) = w 2 + 3 * w 3 + w 4 := by
      refine (Q 3 (fun M => w (M + 1))).trans ?_
      show Tr (Tr (Tr (fun M => w (M + 1)))) 0 = _
      simp [Tr]
      ring
    show 2 * Sd 4 3 w = _
    rw [h, C2 0, Z 2 3 w (by omega), if_pos rfl, q]
    simp
    ring
  | succ m ih =>
    intro w
    have h : Sd (m + 1 + 4) 3 w = Sd (m + 4) 2 (fun M => (M - 1) * w M) + Sd (m + 4) 3 w +
        (if 2 = m + 3 then ∑ t ∈ R (m + 4), w (Finset.univ.sup t + 1) else 0) :=
      step_succ (m + 3) 2 w
    have h2 := ih w
    rw [h, C2 (m + 1), if_neg (by omega)]
    simp
    linarith

lemma C4 (m : ℕ) :
    6 * Sd (m + 5) 4 (fun _ => 1) = (m + 3) * (m ^ 2 + 18 * m + 62) := by
  induction m with
  | zero =>
    have h : Sd 5 4 (fun _ => 1) = Sd 4 3 (fun M => (M - 1) * 1) + Sd 4 4 (fun _ => 1) +
        (if 3 = 3 then ∑ t ∈ R 4, (fun _ : ℕ => 1) (Finset.univ.sup t + 1) else 0) :=
      step_succ 3 3 (fun _ => 1)
    have q : ∑ t ∈ R 4, (fun _ : ℕ => 1) (Finset.univ.sup t + 1) = 15 :=
      (Q 4 (fun _ => 1)).trans (by decide)
    have h3 := C3 0 (fun M => (M - 1) * 1)
    simp at h3
    show 6 * Sd 5 4 (fun _ => 1) = _
    rw [h, Z 3 4 _ (by omega), if_pos rfl, q]
    simp
    omega
  | succ m ih =>
    have h : Sd (m + 1 + 5) 4 (fun _ => 1) = Sd (m + 5) 3 (fun M => (M - 1) * 1) +
        Sd (m + 5) 4 (fun _ => 1) +
        (if 3 = m + 4 then ∑ t ∈ R (m + 5), (fun _ : ℕ => 1) (Finset.univ.sup t + 1) else 0) :=
      step_succ (m + 4) 3 (fun _ => 1)
    have h3 := C3 (m + 1) (fun M => (M - 1) * 1)
    simp at h3
    rw [h, if_neg (by omega)]
    simp
    nlinarith [h3, ih]

lemma mult_add_df {n : ℕ} (s : Fin n → ℕ) :
    (Finset.univ.filter fun i => s i = Finset.univ.sup s).card + df s = n := by
  unfold df
  rw [Finset.card_filter, ← Finset.sum_add_distrib]
  have h : ∀ i : Fin n, (if s i = Finset.univ.sup s then 1 else 0) +
      (if s i = Finset.univ.sup s then 0 else 1) = 1 := fun i => by split_ifs <;> rfl
  simp [h]

lemma T_eq (n k e : ℕ) (h : k + e = n) : T n k = Sd n e (fun _ => 1) := by
  unfold T Sd
  have e1 : {s : Fin n → ℕ | IsRGF s ∧
      (Finset.univ.filter fun i => s i = Finset.univ.sup s).card = k} =
      ((R n).filter fun s => df s = e : Finset (Fin n → ℕ)) := by
    ext s
    simp only [Set.mem_setOf_eq, Finset.coe_filter, mem_R]
    have h2 := mult_add_df s
    refine and_congr Iff.rfl ?_
    omega
  rw [e1, Set.ncard_coe_finset, Finset.card_filter]

end OMA.P124496

open OMA.S_oeis_a124496 OMA.P124496 in
theorem OMA.solution : type_of% @OMA.S_oeis_a124496.main := by
  constructor
  · intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    have h := C3 m (fun _ => 1)
    rw [T_eq (4 + m) (4 + m - 3) 3 (by omega), add_comm 4 m]
    unfold A000096
    have e : m + 4 - 1 = m + 3 := by omega
    rw [e]
    symm
    apply Nat.div_eq_of_eq_mul_right (by norm_num)
    linarith
  · intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    have h := C4 m
    rw [T_eq (5 + m) (5 + m - 4) 4 (by omega), add_comm 5 m]
    unfold A055831
    have e : m + 5 + 1 - 3 = m + 3 := by omega
    have e2 : (m + 5 + 1) ^ 2 + 6 * (m + 5 + 1) - 10 = m ^ 2 + 18 * m + 62 :=
      Nat.sub_eq_of_eq_add (by ring)
    rw [e, e2]
    symm
    apply Nat.div_eq_of_eq_mul_right (by norm_num)
    linarith
