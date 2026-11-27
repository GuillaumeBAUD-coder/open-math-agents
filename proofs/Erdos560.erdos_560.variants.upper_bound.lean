import FormalConjectures.ErdosProblems.«560»

/-! Upper bound `r̂(K_{n,n}) < (3/2) n^3 2^n`, following the counting argument of
Erdős–Faudree–Rousseau–Schelp: take `F = K_{a,2m}` with `m = ⌊n²/4⌋ + n`. For a 2-colouring,
each left vertex has `C(r,n) + C(2m-r,n) ≥ 2 C(m,n)` monochromatic `n`-subsets of the right side
(convexity of binomials), so if `a C(m,n) > (n-1) C(2m,n)` some `n`-subset with a colour is
monochromatically joined to `n` left vertices. The ratio `C(2m,n)/C(m,n) ≤ e 2^n` follows from
`1 + x ≤ eˣ`; small `n ≤ 32` are checked by kernel computation. -/

open SimpleGraph Finset

namespace OMA560
-- convexity
lemma conv_aux (n m : ℕ) : ∀ d r, r + d = m → 2 * m.choose (n+1) ≤ r.choose (n+1) + (2*m - r).choose (n+1) := by
  intro d
  induction d with
  | zero => intro r h; subst h; simp [two_mul]
  | succ d ih =>
    intro r h
    have h1 := ih (r+1) (by omega)
    have e1 : (2*m - r) = (2*m - (r+1)) + 1 := by omega
    rw [e1, Nat.choose_succ_succ' (2*m - (r+1))]
    rw [Nat.choose_succ_succ' r] at h1
    have : r.choose n ≤ (2*m - (r+1)).choose n := Nat.choose_le_choose n (by omega)
    omega

lemma conv (n m r : ℕ) (hr : r ≤ 2*m) : 2 * m.choose n ≤ r.choose n + (2*m - r).choose n := by
  rcases n with _ | n
  · simp
  rcases le_total r m with h | h
  · exact conv_aux n m (m - r) r (by omega)
  · have := conv_aux n m (r - m) (2*m - r) (by omega)
    have e : 2*m - (2*m - r) = r := by omega
    rw [e] at this; omega

-- double counting
lemma dc {a b n : ℕ} (red : Fin a → Finset (Fin b))
    (h : (n-1) * b.choose n * 2 < ∑ x, ((red x).card.choose n + (red x)ᶜ.card.choose n)) :
    ∃ T : Finset (Fin b), T.card = n ∧
      (n ≤ (univ.filter fun x => T ⊆ red x).card ∨ n ≤ (univ.filter fun x => T ⊆ (red x)ᶜ).card) := by
  by_contra hc
  push_neg at hc
  have key : ∀ f : Fin a → Finset (Fin b), ∑ x, (f x).card.choose n =
      ∑ T ∈ powersetCard n (univ : Finset (Fin b)), (univ.filter fun x => T ⊆ f x).card := by
    intro f
    simp_rw [← Finset.card_powersetCard, card_eq_sum_ones, sum_filter]
    rw [Finset.sum_comm]
    refine sum_congr rfl fun x _ => ?_
    rw [← sum_filter]
    congr 1
    ext T; simp [mem_powersetCard, and_comm]
  have hsum : ∑ x, ((red x).card.choose n + (red x)ᶜ.card.choose n) ≤ (n-1) * b.choose n * 2 := by
    rw [sum_add_distrib, key red, key (fun x => (red x)ᶜ)]
    have h1 : ∀ g : Finset (Fin b) → ℕ, (∀ T ∈ powersetCard n (univ : Finset (Fin b)), g T ≤ n - 1) →
        ∑ T ∈ powersetCard n (univ : Finset (Fin b)), g T ≤ (n-1) * b.choose n := by
      intro g hg
      calc _ ≤ ∑ T ∈ powersetCard n (univ : Finset (Fin b)), (n-1) := sum_le_sum hg
        _ = _ := by simp [card_powersetCard, mul_comm]
    have A := h1 (fun T => (univ.filter fun x => T ⊆ red x).card)
      (fun T hT => by have := (hc T (mem_powersetCard.1 hT).2).1; omega)
    have B := h1 (fun T => (univ.filter fun x => T ⊆ (red x)ᶜ).card)
      (fun T hT => by have := (hc T (mem_powersetCard.1 hT).2).2; omega)
    omega
  omega

def Fab (a b : ℕ) : SimpleGraph (Fin (a+b)) :=
  SimpleGraph.fromRel (fun u v => u.val < a ∧ a ≤ v.val)

lemma Fab_adj (a b : ℕ) (x : Fin a) (y : Fin b) : (Fab a b).Adj (Fin.castAdd b x) (Fin.natAdd a y) := by
  simp only [Fab, fromRel_adj]
  refine ⟨?_, Or.inl ⟨by simp, by simp⟩⟩
  intro h; have := congrArg Fin.val h; simp at this; omega

lemma Fab_edges (a b : ℕ) : (Fab a b).edgeSet.ncard = a * b := by
  have : (Fab a b).edgeSet = Set.range (fun p : Fin a × Fin b => s(Fin.castAdd b p.1, Fin.natAdd a p.2)) := by
    ext e
    induction e using Sym2.ind with
    | _ u v =>
    simp only [mem_edgeSet, Set.mem_range, Prod.exists]
    constructor
    · intro h
      simp only [Fab, fromRel_adj] at h
      rcases h with ⟨_, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
      · refine ⟨⟨u.val, h1⟩, ⟨v.val - a, by omega⟩, ?_⟩
        rw [Sym2.eq_iff]; left; constructor <;> ext <;> simp; omega
      · refine ⟨⟨v.val, h1⟩, ⟨u.val - a, by omega⟩, ?_⟩
        rw [Sym2.eq_iff]; right; constructor <;> ext <;> simp; omega
    · rintro ⟨x, y, h⟩
      have := Fab_adj a b x y
      rw [← mem_edgeSet, h] at this; exact this
  rw [this, Set.ncard_range_of_injective, Nat.card_eq_fintype_card]
  · simp
  · rintro ⟨x, y⟩ ⟨x', y'⟩ h
    simp only [Sym2.eq_iff] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp [Fin.castAdd_inj] at h1 h2; simp [h1, h2]
    · have := congrArg Fin.val h1; simp at this; omega

-- embedding lemma
lemma embed {V : Type*} (G : SimpleGraph V) {a b n : ℕ} (f : Fin a → V) (g : Fin b → V)
    (hf : Function.Injective f) (hg : Function.Injective g) (hfg : ∀ x y, f x ≠ g y)
    (S : Finset (Fin a)) (T : Finset (Fin b)) (hS : S.card = n) (hT : T.card = n)
    (hadj : ∀ x ∈ S, ∀ y ∈ T, G.Adj (f x) (g y)) :
    (completeBipartiteGraph (Fin n) (Fin n)).IsContained G := by
  let φ : Fin n ⊕ Fin n → V := fun s => match s with
    | Sum.inl i => f (S.orderEmbOfFin hS i)
    | Sum.inr j => g (T.orderEmbOfFin hT j)
  refine ⟨⟨⟨φ, ?_⟩, ?_⟩⟩
  · rintro (i | i) (j | j) h <;> simp at h
    · exact hadj _ (S.orderEmbOfFin_mem hS i) _ (T.orderEmbOfFin_mem hT j)
    · exact (hadj _ (S.orderEmbOfFin_mem hS j) _ (T.orderEmbOfFin_mem hT i)).symm
  · rintro (i | i) (j | j) h
    · simp only [φ] at h; rw [(S.orderEmbOfFin hS).injective (hf h)]
    · exact absurd h (hfg _ _)
    · exact absurd h.symm (hfg _ _)
    · simp only [φ] at h; rw [(T.orderEmbOfFin hT).injective (hg h)]

lemma ramsey_bound (n m a : ℕ) (h : (n-1) * (2*m).choose n < a * m.choose n) :
    sizeRamsey (completeBipartiteGraph (Fin n) (Fin n)) (completeBipartiteGraph (Fin n) (Fin n))
      ≤ a * (2*m) := by
  classical
  refine Nat.sInf_le ⟨a + 2*m, Fab a (2*m), Fab_edges a (2*m), fun R hR => ?_⟩
  let red : Fin a → Finset (Fin (2*m)) := fun x =>
    univ.filter fun y => R.Adj (Fin.castAdd (2*m) x) (Fin.natAdd a y)
  have hsum : (n-1) * (2*m).choose n * 2 <
      ∑ x, ((red x).card.choose n + (red x)ᶜ.card.choose n) := by
    have : ∀ x, 2 * m.choose n ≤ (red x).card.choose n + (red x)ᶜ.card.choose n := by
      intro x
      have hc : (red x)ᶜ.card = 2*m - (red x).card := by
        rw [card_compl, Fintype.card_fin]
      rw [hc]
      exact conv n m _ (by simpa using card_le_univ (red x))
    calc (n-1) * (2*m).choose n * 2 < a * (2 * m.choose n) := by nlinarith
      _ = ∑ _x : Fin a, 2 * m.choose n := by simp
      _ ≤ _ := sum_le_sum fun x _ => this x
  obtain ⟨T, hT, hc⟩ := dc red hsum
  have hf : Function.Injective (Fin.castAdd (2*m) : Fin a → Fin (a + 2*m)) := Fin.castAdd_injective _ _
  have hg : Function.Injective (Fin.natAdd a : Fin (2*m) → Fin (a + 2*m)) := Fin.natAdd_injective _ _
  have hfg : ∀ x y, (Fin.castAdd (2*m) x : Fin (a + 2*m)) ≠ Fin.natAdd a y := by
    intro x y h; have := congrArg Fin.val h; simp at this; omega
  rcases hc with hc | hc
  · obtain ⟨S, hS1, hS2⟩ := exists_subset_card_eq hc
    left
    refine embed R _ _ hf hg hfg S T hS2 hT fun x hx y hy => ?_
    have := (mem_filter.1 (hS1 hx)).2 hy
    simpa [red] using this
  · obtain ⟨S, hS1, hS2⟩ := exists_subset_card_eq hc
    right
    refine embed _ _ _ hf hg hfg S T hS2 hT fun x hx y hy => ?_
    have := (mem_filter.1 (hS1 hx)).2 hy
    simp only [red, mem_compl, mem_filter, mem_univ, true_and] at this
    exact (sdiff_adj _ _ _ _).2 ⟨Fab_adj a (2*m) x y, this⟩
lemma small_ok : ∀ n, 1 ≤ n → n ≤ 32 →
    2 * (((n-1) * (2*(n*n/4+n)).descFactorial n / (n*n/4+n).descFactorial n + 1) * (2*(n*n/4+n)))
      < 3 * n^3 * 2^n := by
  decide +kernel

lemma desc_bound (m n : ℕ) (c : ℝ) (hc : 0 < c) (hcm : c ≤ (m:ℝ) - n + 1) :
    ∀ j ≤ n, ((2*m).descFactorial j : ℝ) ≤
      2^j * (m.descFactorial j : ℝ) * Real.exp ((j:ℝ) * (j - 1) / (4 * c)) := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have ih := ih (by omega)
    have hjm : j < m := by
      have : (j:ℝ) + 1 ≤ n := by exact_mod_cast hj
      have : (j:ℝ) < m := by linarith
      exact_mod_cast this
    rw [Nat.descFactorial_succ, Nat.descFactorial_succ]
    push_cast [show j ≤ 2*m by omega, hjm.le]
    have hmj : c ≤ (m:ℝ) - j := by
      have : (j:ℝ) + 1 ≤ n := by exact_mod_cast hj
      linarith
    have hexp : Real.exp ((((j:ℝ)+1) * ((j:ℝ) + 1 - 1)) / (4 * c)) =
        Real.exp ((j:ℝ) * (j - 1) / (4 * c)) * Real.exp (j / (2*c)) := by
      rw [← Real.exp_add]; congr 1; field_simp; ring
    rw [hexp]
    have h1 : (2 * (m:ℝ) - j) ≤ 2 * ((m:ℝ) - j) * Real.exp (j / (2*c)) := by
      have e1 := Real.add_one_le_exp (j / (2*c))
      have hj0 : (0:ℝ) ≤ j := by positivity
      have : (2 * (m:ℝ) - j) ≤ 2 * ((m:ℝ) - j) * (j / (2*c) + 1) := by
        rw [show 2 * ((m:ℝ) - j) * (j / (2*c) + 1) = 2 * ((m:ℝ) - j) + ((m:ℝ) - j) / c * j by
          field_simp; ring]
        have : 1 ≤ ((m:ℝ) - j) / c := by rw [le_div_iff₀ hc]; linarith
        nlinarith
      have : 0 ≤ 2 * ((m:ℝ) - j) := by linarith
      nlinarith
    have hA : (0:ℝ) ≤ (2*m).descFactorial j := by positivity
    have hB : (0:ℝ) ≤ 2 * (m:ℝ) - j := by linarith
    calc (2 * (m:ℝ) - j) * ((2*m).descFactorial j : ℝ)
        ≤ (2 * ((m:ℝ) - j) * Real.exp (j / (2*c))) *
            (2^j * (m.descFactorial j : ℝ) * Real.exp ((j:ℝ) * (j - 1) / (4 * c))) :=
          mul_le_mul h1 ih hA (mul_nonneg (by linarith) (Real.exp_pos _).le)
      _ = _ := by ring

lemma choose_ratio (n : ℕ) (hn : 1 ≤ n) :
    (((2*(n*n/4+n)).choose n : ℕ) : ℝ) ≤ 2^n * Real.exp 1 * ((n*n/4+n).choose n : ℝ) := by
  set m := n*n/4+n with hm
  have hk : n*n ≤ 4*(n*n/4) + 3 := by omega
  have hcpos : (0:ℝ) < (m:ℝ) - n + 1 := by
    have : n ≤ m := by omega
    have : (n:ℝ) ≤ m := by exact_mod_cast this
    linarith
  have hd := desc_bound m n ((m:ℝ) - n + 1) hcpos le_rfl n le_rfl
  have hexp : Real.exp ((n:ℝ) * (n - 1) / (4 * ((m:ℝ) - n + 1))) ≤ Real.exp 1 := by
    apply Real.exp_le_exp.2
    rw [div_le_one (by linarith)]
    have : ((n*n : ℕ) : ℝ) ≤ 4*((n*n/4 : ℕ) : ℝ) + 3 := by exact_mod_cast hk
    have hm' : (m:ℝ) = ((n*n/4 : ℕ) : ℝ) + n := by rw [hm]; push_cast; ring
    push_cast at this
    rw [hm']; nlinarith
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose] at hd
  push_cast at hd
  have hf : (0:ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have h2 : (0:ℝ) ≤ 2^n * ((n.factorial : ℝ) * (m.choose n : ℝ)) := by positivity
  have : (n.factorial : ℝ) * ((2*m).choose n : ℝ) ≤ (n.factorial : ℝ) * (2^n * Real.exp 1 * (m.choose n : ℝ)) := by
    calc _ ≤ 2 ^ n * (↑n.factorial * ↑(m.choose n)) * Real.exp (↑n * (↑n - 1) / (4 * (↑m - ↑n + 1))) := hd
      _ ≤ 2 ^ n * (↑n.factorial * ↑(m.choose n)) * Real.exp 1 := mul_le_mul_of_nonneg_left hexp h2
      _ = _ := by ring
  exact le_of_mul_le_mul_left this hf

lemma numeric (n : ℕ) (hn : 1 ≤ n) :
    ((((n-1) * (2*(n*n/4+n)).choose n / (n*n/4+n).choose n + 1) * (2*(n*n/4+n)) : ℕ) : ℝ)
      < 3/2 * n^3 * 2^n := by
  set m := n*n/4+n with hm
  rcases le_or_gt n 32 with hs | hl
  · have h := small_ok n hn hs
    rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose,
      show (n-1) * (n.factorial * (2*m).choose n) = n.factorial * ((n-1) * (2*m).choose n) by ring,
      Nat.mul_div_mul_left _ _ (Nat.factorial_pos n)] at h
    have : ((2 * (((n-1) * (2*m).choose n / m.choose n + 1) * (2*m)) : ℕ) : ℝ) < ((3 * n^3 * 2^n : ℕ) : ℝ) := by
      exact_mod_cast h
    push_cast at this ⊢
    linarith
  · have hcm : (0:ℝ) < (m.choose n : ℝ) := by
      have : n ≤ m := by omega
      exact_mod_cast Nat.choose_pos this
    have hq : (((n-1) * (2*m).choose n / m.choose n : ℕ) : ℝ) ≤ ((n:ℝ) - 1) * 2^n * Real.exp 1 := by
      refine (Nat.cast_div_le).trans ?_
      rw [div_le_iff₀ hcm]
      have := choose_ratio n hn
      push_cast [hn]
      have h0 : (0:ℝ) ≤ (n:ℝ) - 1 := by
        have : (1:ℝ) ≤ n := by exact_mod_cast hn
        linarith
      calc ((n:ℝ) - 1) * ((2*m).choose n : ℝ) ≤ ((n:ℝ) - 1) * (2^n * Real.exp 1 * (m.choose n : ℝ)) :=
            mul_le_mul_of_nonneg_left this h0
        _ = _ := by ring
    have hmr : (m:ℝ) ≤ (n:ℝ)^2/4 + n := by
      have h1 : 4*(n*n/4) ≤ n*n := Nat.mul_div_le (n*n) 4
      have h2 : ((4*(n*n/4) : ℕ) : ℝ) ≤ ((n*n : ℕ) : ℝ) := by exact_mod_cast h1
      have hm' : (m:ℝ) = ((n*n/4 : ℕ) : ℝ) + n := by rw [hm]; push_cast; ring
      push_cast at h2
      rw [hm']; nlinarith
    have he := Real.exp_one_lt_d9
    have hX : (1:ℝ) ≤ 2^n := one_le_pow₀ (by norm_num)
    have hn33 : (33:ℝ) ≤ n := by exact_mod_cast hl
    push_cast
    set q : ℝ := (((n-1) * (2*m).choose n / m.choose n : ℕ) : ℝ)
    set X : ℝ := 2^n
    have hq0 : 0 ≤ q := by positivity
    have hm0 : (0:ℝ) ≤ m := by positivity
    have step1 : (q + 1) * (2 * (m:ℝ)) ≤ (((n:ℝ) - 1) * X * 2.72 + X) * ((n:ℝ)^2/2 + 2*n) := by
      have : q + 1 ≤ ((n:ℝ) - 1) * X * 2.72 + X := by
        have : ((n:ℝ) - 1) * X * Real.exp 1 ≤ ((n:ℝ) - 1) * X * 2.72 := by
          apply mul_le_mul_of_nonneg_left (by linarith)
          apply mul_nonneg (by linarith) (by linarith)
        linarith
      have h2m : 2 * (m:ℝ) ≤ (n:ℝ)^2/2 + 2*n := by linarith
      calc (q + 1) * (2 * (m:ℝ)) ≤ (((n:ℝ) - 1) * X * 2.72 + X) * (2 * (m:ℝ)) :=
            mul_le_mul_of_nonneg_right this (by linarith)
        _ ≤ _ := mul_le_mul_of_nonneg_left h2m (by nlinarith)
    have step2 : (((n:ℝ) - 1) * 2.72 + 1) * ((n:ℝ)^2/2 + 2*n) < 3/2 * (n:ℝ)^3 := by
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ n - 33) (by linarith : (0:ℝ) ≤ n)]
    have : (((n:ℝ) - 1) * X * 2.72 + X) * ((n:ℝ)^2/2 + 2*n) = X * ((((n:ℝ) - 1) * 2.72 + 1) * ((n:ℝ)^2/2 + 2*n)) := by ring
    nlinarith

end OMA560

theorem OMA.solution : type_of% @Erdos560.erdos_560.variants.upper_bound := by
  intro n hn
  set m := n*n/4+n with hm
  have hY : 0 < m.choose n := Nat.choose_pos (by omega)
  have hlt : (n-1) * (2*m).choose n < ((n-1) * (2*m).choose n / m.choose n + 1) * m.choose n := by
    rw [add_mul, one_mul]; exact Nat.lt_div_mul_add hY
  have hb := OMA560.ramsey_bound n m _ hlt
  have hb' : (sizeRamsey (completeBipartiteGraph (Fin n) (Fin n))
      (completeBipartiteGraph (Fin n) (Fin n)) : ℝ) ≤
      ((((n-1) * (2*m).choose n / m.choose n + 1) * (2*m) : ℕ) : ℝ) := by exact_mod_cast hb
  exact lt_of_le_of_lt hb' (OMA560.numeric n hn)
