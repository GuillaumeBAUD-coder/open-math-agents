import FormalConjectures.Arxiv.«0805.3777».TensorRank

-- Reduction Arxiv.0805.3777.isMaxRank_of_le_min.R1 of Generic and maximal rank of 3-tensors — isMaxRank of le min
-- Credit: @ivillar
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# The maximal rank of `m × n × (m n - u)` tensors for `u ≤ 4`: reduction to two statements

The statement: for 3 <= m <= n and u <= min(4, m), the maximal rank of an m x n x (m n - u) tensor
is m n - ceil(u / 2) (Atkinson and Stephens 1979; Bruzda, Friedland, Zyczkowski, (4.24)).

Framing. A tensor T with slices T_1, ..., T_p (m x n matrices) has rank at most r exactly when
the slices lie in the span of r rank-one matrices x_l y_l^T (a cover of the slice space by r
rank-one matrices). Both directions of this dictionary are proved below (cprank_le_of_cover,
cover_of_cprank_le, exists_holor), so that the two hypotheses are statements about subspaces of
m x n matrices.

H1 is the upper bound for u = 3 (which contains the one for u = 4): a subspace of codimension at
least 3 lies in the span of m n - 2 rank-one matrices. Equivalently, every space of matrices of
dimension 3 contains a pencil whose orthogonal complement is spanned by rank-one matrices.
H2 is the lower bound for u = 4: for 4 <= m <= n some subspace of codimension at least 4 lies in
no span of m n - 3 rank-one matrices.

A remark towards H1. Let U be the orthogonal complement of S for the pairing sum_ij A_ij B_ij; it
has dimension at least 3, and it is enough to find independent B, C in U such that the rank-one
matrices x y^T with x^T B y = x^T C y = 0 span the orthogonal complement of {B, C}. This holds for
instance when B = a b^T has rank one and C is not of the form a z^T + w b^T: the rank-one matrices
with a^T x = 0 and x^T C y = 0, and those with b^T y = 0 and x^T C y = 0, span two spaces (by the
argument of ker_le_span_r1 below) whose sum is that complement. It fails for B = E_00 + E_11 and
C = E_01, the example behind the lower bounds below, so the choice of the pencil in U matters.

What main proves without the hypotheses.
* Upper bound, u = 0: the m n matrix units are rank-one matrices.
* Upper bound, u = 1, 2: a subspace S of dimension less than m n lies in the kernel of a nonzero
  functional phi (the pairing with a nonzero matrix B orthogonal to S), and the kernel of phi is
  spanned by the rank-one matrices it contains (ker_le_span_r1): fix a rank-one E = a b^T with
  phi(E) nonzero; then x b^T and a y^T differ from a rank-one matrix in ker phi by a multiple of
  E, and for suitable s, t the rank-one matrix (x + s a)(y + t b)^T lies in ker phi and differs
  from x y^T by multiples of x b^T, a y^T and E. A basis extracted from these rank-one matrices
  has at most m n - 1 elements.
* Lower bound, u = 0: the whole matrix space has dimension m n.
* Lower bound, u = 1, 2, 3 (no_cover_ker, no_cover_two, no_cover_three): let S be the space of
  matrices A with A_00 + A_11 = 0 and A_01 = 0 (and A_22 = 0 for u = 3), of codimension u = 2, 3.
  A rank-one matrix x y^T in S has x_0 y_1 = 0 and x_0 y_0 = - x_1 y_1, hence (x_0 y_0)^2 = 0. So
  a span of m n - u rank-one matrices that contains S would be equal to S and consist of matrices
  with vanishing (0, 0) entry, while E_00 - E_11 lies in S. For u = 1 the same space is used.

Reuse and credit: the Holor plumbing (headI_lt, ix_surj, cprank_le_of_cprankMax,
cprank_le_of_sum, cprankMax1_cons, exists_sum_of_cprankMax, cprankMax_cprank) follows the Bridge
sections of the merged proofs proofs/Arxiv.0805.3777.cprank_le_of_three_slices.lean (PR #3512) and
proofs/Arxiv.0805.3777.isMaxRank_three.lean (PR #3653), both by the same owner, which adapted it
from proofs/Arxiv.0805.3777.isMaxRank_three_three_five_bounds.lean (PR #2438, DomTheDeveloper; a
port of Kenta Kitamura's https://github.com/KitaKen1/mrank-3-3-5-lean, Apache License 2.0). It is
written here without definitions, since a reduction file declares none. Everything else is new.
-/

namespace OMA.R_Arxiv_0805_3777_isMaxRank_of_le_min_R1

open Matrix

def H1 : Prop :=
  ∀ (m n : ℕ), 3 ≤ m → m ≤ n → ∀ S : Submodule ℂ (Matrix (Fin m) (Fin n) ℂ),
    Module.finrank ℂ S + 3 ≤ m * n →
    ∃ (x : Fin (m * n - 2) → Fin m → ℂ) (y : Fin (m * n - 2) → Fin n → ℂ),
      S ≤ Submodule.span ℂ (Set.range fun l => Matrix.vecMulVec (x l) (y l))

def H2 : Prop :=
  ∀ (m n : ℕ), 4 ≤ m → m ≤ n → ∃ S : Submodule ℂ (Matrix (Fin m) (Fin n) ℂ),
    Module.finrank ℂ S + 4 ≤ m * n ∧
    ∀ (x : Fin (m * n - 3) → Fin m → ℂ) (y : Fin (m * n - 3) → Fin n → ℂ),
      ¬ S ≤ Submodule.span ℂ (Set.range fun l => Matrix.vecMulVec (x l) (y l))

-- ### Holor plumbing

theorem headI_lt {d : ℕ} {ds : List ℕ} (t : HolorIndex (d :: ds)) : t.1.headI < d := by
  obtain ⟨l, h⟩ := t
  cases h with
  | cons ha _ => exact ha

theorem tail_forall {d : ℕ} {ds : List ℕ} (t : HolorIndex (d :: ds)) :
    List.Forall₂ (· < ·) t.1.tail ds := by
  obtain ⟨l, h⟩ := t
  cases h with
  | cons _ h => exact h

theorem ix_surj {d₁ d₂ d₃ : ℕ} (t : HolorIndex [d₁, d₂, d₃]) :
    ∃ (c : Fin d₁) (i : Fin d₂) (j : Fin d₃),
      t = ⟨[c.1, i.1, j.1], .cons c.2 (.cons i.2 (.cons j.2 .nil))⟩ := by
  obtain ⟨l, h⟩ := t
  cases h with
  | cons ha h =>
    cases h with
    | cons hb h =>
      cases h with
      | cons hc h =>
        cases h
        exact ⟨⟨_, ha⟩, ⟨_, hb⟩, ⟨_, hc⟩, rfl⟩

theorem cprank_le_of_cprankMax {ds : List ℕ} {x : Holor ℂ ds} {k : ℕ}
    (h : Holor.CPRankMax k x) : x.cprank ≤ k :=
  @Nat.find_min' (fun n => Holor.CPRankMax n x) (Classical.decPred _)
    ⟨ds.prod, Holor.cprankMax_upper_bound x⟩ k h

theorem cprankMax_cprank {ds : List ℕ} (x : Holor ℂ ds) : Holor.CPRankMax x.cprank x :=
  @Nat.find_spec (fun k => Holor.CPRankMax k x) (Classical.decPred _)
    ⟨ds.prod, Holor.cprankMax_upper_bound x⟩

theorem holor_sum_apply {ds : List ℕ} {β : Type} (s : Finset β) (f : β → Holor ℂ ds)
    (t : HolorIndex ds) : (∑ l ∈ s, f l) t = ∑ l ∈ s, f l t := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    rfl

/-- A tensor whose entries are a sum of products has rank at most the number of summands. -/
theorem cprank_le_of_sum {d₁ d₂ d₃ : ℕ} {ι : Type} [Fintype ι] (T : Holor ℂ [d₁, d₂, d₃])
    (u : ι → Fin d₁ → ℂ) (v : ι → Fin d₂ → ℂ) (w : ι → Fin d₃ → ℂ)
    (h : ∀ (c : Fin d₁) (i : Fin d₂) (j : Fin d₃),
      T ⟨[c.1, i.1, j.1], .cons c.2 (.cons i.2 (.cons j.2 .nil))⟩ =
        ∑ l, u l c * v l i * w l j) :
    T.cprank ≤ Fintype.card ι := by
  classical
  have hR : ∀ l, Holor.CPRankMax1
      (Holor.mul (fun t : HolorIndex [d₁] => u l ⟨t.1.headI, headI_lt t⟩)
        (Holor.mul (fun t : HolorIndex [d₂] => v l ⟨t.1.headI, headI_lt t⟩)
          (Holor.mul (fun t : HolorIndex [d₃] => w l ⟨t.1.headI, headI_lt t⟩)
            (fun _ : HolorIndex [] => (1 : ℂ))))) :=
    fun l => .cons _ _ (.cons _ _ (.cons _ _ (.nil _)))
  have hT : T = ∑ l, Holor.mul (fun t : HolorIndex [d₁] => u l ⟨t.1.headI, headI_lt t⟩)
      (Holor.mul (fun t : HolorIndex [d₂] => v l ⟨t.1.headI, headI_lt t⟩)
        (Holor.mul (fun t : HolorIndex [d₃] => w l ⟨t.1.headI, headI_lt t⟩)
          (fun _ : HolorIndex [] => (1 : ℂ)))) := by
    funext t
    obtain ⟨c, i, j, rfl⟩ := ix_surj t
    rw [h]
    refine Eq.trans ?_ (holor_sum_apply Finset.univ _ _).symm
    refine Finset.sum_congr rfl fun l _ => ?_
    show _ = u l c * (v l i * (w l j * 1))
    ring
  have hr := Holor.cprankMax_sum (n := 1) Finset.univ _ fun l _ => Holor.cprankMax_1 (hR l)
  rw [Finset.card_univ, mul_one, ← hT] at hr
  exact cprank_le_of_cprankMax hr

/-- If all slices lie in the span of `r` rank-one matrices, the tensor has rank at most `r`. -/
theorem cprank_le_of_cover {m n p r : ℕ} (T : Holor ℂ [m, n, p])
    (x : Fin r → Fin m → ℂ) (y : Fin r → Fin n → ℂ)
    (h : ∀ k : Fin p, (Matrix.of fun (i : Fin m) (j : Fin n) =>
        T ⟨[i.1, j.1, k.1], .cons i.2 (.cons j.2 (.cons k.2 .nil))⟩ :
          Matrix (Fin m) (Fin n) ℂ) ∈
      Submodule.span ℂ (Set.range fun l => vecMulVec (x l) (y l))) : T.cprank ≤ r := by
  classical
  have hc : ∀ k : Fin p, ∃ c : Fin r → ℂ, ∑ l, c l • vecMulVec (x l) (y l) =
      (Matrix.of fun (i : Fin m) (j : Fin n) =>
        T ⟨[i.1, j.1, k.1], .cons i.2 (.cons j.2 (.cons k.2 .nil))⟩ :
          Matrix (Fin m) (Fin n) ℂ) :=
    fun k => (Submodule.mem_span_range_iff_exists_fun ℂ).mp (h k)
  choose c hc using hc
  refine le_of_le_of_eq (cprank_le_of_sum T x y (fun l k => c k l) ?_) (Fintype.card_fin r)
  intro i j k
  have h1 := congrFun (congrFun (hc k) i) j
  rw [Matrix.of_apply] at h1
  rw [← h1, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
  ring

theorem cprankMax1_cons {α : Type} [Mul α] {d : ℕ} {ds : List ℕ} {x : Holor α (d :: ds)}
    (h : Holor.CPRankMax1 x) :
    ∃ (u : Holor α [d]) (y : Holor α ds), Holor.CPRankMax1 y ∧ x = Holor.mul u y := by
  cases h with
  | cons u y hy => exact ⟨u, y, hy, rfl⟩

theorem cprankMax1_apply {m n p : ℕ} {x : Holor ℂ [m, n, p]} (h : Holor.CPRankMax1 x) :
    ∃ (u : Fin m → ℂ) (v : Fin n → ℂ) (w : Fin p → ℂ),
      ∀ (i : Fin m) (j : Fin n) (k : Fin p),
        x ⟨[i.1, j.1, k.1], .cons i.2 (.cons j.2 (.cons k.2 .nil))⟩ = u i * v j * w k := by
  obtain ⟨u₁, y₁, h₁, rfl⟩ := cprankMax1_cons h
  obtain ⟨u₂, y₂, h₂, rfl⟩ := cprankMax1_cons h₁
  obtain ⟨u₃, y₃, -, rfl⟩ := cprankMax1_cons h₂
  refine ⟨fun i => u₁ ⟨[i.1], .cons i.2 .nil⟩, fun j => u₂ ⟨[j.1], .cons j.2 .nil⟩,
    fun k => u₃ ⟨[k.1], .cons k.2 .nil⟩ * y₃ ⟨[], .nil⟩, fun i j k => ?_⟩
  show u₁ ⟨[i.1], .cons i.2 .nil⟩ * (u₂ ⟨[j.1], .cons j.2 .nil⟩ *
    (u₃ ⟨[k.1], .cons k.2 .nil⟩ * y₃ ⟨[], .nil⟩)) = _
  ring

theorem exists_sum_of_cprankMax {α : Type} [Mul α] [AddCommMonoid α] {ds : List ℕ} {k : ℕ}
    {x : Holor α ds} (h : Holor.CPRankMax k x) :
    ∃ f : Fin k → Holor α ds, (∀ l, Holor.CPRankMax1 (f l)) ∧ x = ∑ l, f l := by
  induction h with
  | zero => exact ⟨Fin.elim0, fun l => l.elim0, by simp⟩
  | succ k x y hx _ ih =>
    obtain ⟨f, hf, rfl⟩ := ih
    refine ⟨Fin.cons x f, fun l => Fin.cases hx hf l, ?_⟩
    rw [Fin.sum_univ_succ]
    rfl

/-- Enlarging a family of rank-one matrices by zero matrices. -/
theorem pad_cover {m n c r : ℕ} (hcr : c ≤ r) (x : Fin c → Fin m → ℂ) (y : Fin c → Fin n → ℂ) :
    ∃ (x' : Fin r → Fin m → ℂ) (y' : Fin r → Fin n → ℂ),
      Submodule.span ℂ (Set.range fun l => vecMulVec (x l) (y l)) ≤
        Submodule.span ℂ (Set.range fun l => vecMulVec (x' l) (y' l)) := by
  refine ⟨fun l => if h : l.1 < c then x ⟨l.1, h⟩ else 0,
    fun l => if h : l.1 < c then y ⟨l.1, h⟩ else 0, Submodule.span_mono ?_⟩
  rintro _ ⟨i, rfl⟩
  refine ⟨⟨i.1, lt_of_lt_of_le i.2 hcr⟩, ?_⟩
  simp only [dif_pos i.2]

/-- A tensor of rank at most `r` has its slices in the span of `r` rank-one matrices. -/
theorem cover_of_cprank_le {m n p r : ℕ} (T : Holor ℂ [m, n, p]) (hr : T.cprank ≤ r) :
    ∃ (x : Fin r → Fin m → ℂ) (y : Fin r → Fin n → ℂ), ∀ k : Fin p,
      (Matrix.of fun (i : Fin m) (j : Fin n) =>
        T ⟨[i.1, j.1, k.1], .cons i.2 (.cons j.2 (.cons k.2 .nil))⟩ :
          Matrix (Fin m) (Fin n) ℂ) ∈
      Submodule.span ℂ (Set.range fun l => vecMulVec (x l) (y l)) := by
  obtain ⟨f, hf, hsum⟩ := exists_sum_of_cprankMax (cprankMax_cprank T)
  choose u v w huvw using fun l => cprankMax1_apply (hf l)
  obtain ⟨x, y, hxy⟩ := pad_cover hr u v
  refine ⟨x, y, fun k => hxy ?_⟩
  have e : (Matrix.of fun (i : Fin m) (j : Fin n) =>
      T ⟨[i.1, j.1, k.1], .cons i.2 (.cons j.2 (.cons k.2 .nil))⟩ :
        Matrix (Fin m) (Fin n) ℂ) = ∑ l, w l k • vecMulVec (u l) (v l) := by
    ext i j
    rw [Matrix.of_apply, Matrix.sum_apply]
    have hT : T ⟨[i.1, j.1, k.1], .cons i.2 (.cons j.2 (.cons k.2 .nil))⟩ =
        ∑ l, f l ⟨[i.1, j.1, k.1], .cons i.2 (.cons j.2 (.cons k.2 .nil))⟩ :=
      (congrFun hsum _).trans (holor_sum_apply Finset.univ f _)
    rw [hT]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [huvw, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
    ring
  rw [e]
  exact Submodule.sum_mem _ fun l _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)

/-- A tensor with prescribed slices. -/
theorem exists_holor {m n p : ℕ} (M : Fin p → Matrix (Fin m) (Fin n) ℂ) :
    ∃ T : Holor ℂ [m, n, p], ∀ (i : Fin m) (j : Fin n) (k : Fin p),
      T ⟨[i.1, j.1, k.1], .cons i.2 (.cons j.2 (.cons k.2 .nil))⟩ = M k i j :=
  ⟨fun t => M
      ⟨t.1.tail.tail.headI, headI_lt (d := p) (ds := [])
        ⟨t.1.tail.tail, tail_forall (d := n) (ds := [p]) ⟨t.1.tail, tail_forall t⟩⟩⟩
      ⟨t.1.headI, headI_lt t⟩
      ⟨t.1.tail.headI, headI_lt (d := n) (ds := [p]) ⟨t.1.tail, tail_forall t⟩⟩,
    fun _ _ _ => rfl⟩

-- ### Spans of rank-one matrices

theorem finrank_matrix_eq (m n : ℕ) :
    Module.finrank ℂ (Matrix (Fin m) (Fin n) ℂ) = m * n := by
  simp [Module.finrank_matrix]

theorem finrank_span_range_le {m n p : ℕ} (M : Fin p → Matrix (Fin m) (Fin n) ℂ) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range M)) ≤ p := by
  have h := finrank_range_le_card (R := ℂ) M
  rwa [Fintype.card_fin] at h

theorem span_r1_top (m n : ℕ) :
    Submodule.span ℂ {M : Matrix (Fin m) (Fin n) ℂ |
      ∃ (a : Fin m → ℂ) (b : Fin n → ℂ), M = vecMulVec a b} = ⊤ := by
  refine eq_top_iff.mpr fun A _ => ?_
  rw [Matrix.matrix_eq_sum_single A]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  have e : Matrix.single i j (A i j) = A i j • vecMulVec (Pi.single i 1) (Pi.single j 1) := by
    rw [← Matrix.single_eq_single_vecMulVec_single, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, _, rfl⟩)

/-- A span of rank-one matrices of dimension at most `r` is covered by `r` rank-one matrices. -/
theorem cover_of_span {m n r : ℕ} (s : Set (Matrix (Fin m) (Fin n) ℂ))
    (hs : ∀ M ∈ s, ∃ (a : Fin m → ℂ) (b : Fin n → ℂ), M = vecMulVec a b)
    (hr : Module.finrank ℂ (Submodule.span ℂ s) ≤ r) :
    ∃ (x : Fin r → Fin m → ℂ) (y : Fin r → Fin n → ℂ),
      Submodule.span ℂ s ≤ Submodule.span ℂ (Set.range fun l => vecMulVec (x l) (y l)) := by
  obtain ⟨f, hf, hspan, -⟩ := Submodule.exists_fun_fin_finrank_span_eq ℂ s
  choose a b hab using fun i => hs (f i) (hf i)
  obtain ⟨x, y, hxy⟩ := pad_cover hr a b
  have e : f = fun l => vecMulVec (a l) (b l) := funext hab
  refine ⟨x, y, le_trans (le_of_eq (hspan.symm.trans ?_)) hxy⟩
  rw [e]

theorem vmv_left {m n : ℕ} (x a : Fin m → ℂ) (b : Fin n → ℂ) (k : ℂ) :
    vecMulVec (x + k • a) b = vecMulVec x b + k • vecMulVec a b := by
  rw [Matrix.add_vecMulVec, Matrix.smul_vecMulVec]

theorem vmv_right {m n : ℕ} (a : Fin m → ℂ) (y b : Fin n → ℂ) (k : ℂ) :
    vecMulVec a (y + k • b) = vecMulVec a y + k • vecMulVec a b := by
  rw [Matrix.vecMulVec_add, Matrix.vecMulVec_smul]

/-- If a subspace `W` contains every rank-one matrix killed by `φ` and one rank-one matrix not
killed by `φ`, it contains every rank-one matrix. -/
theorem r1_mem_of {m n : ℕ} (φ : Matrix (Fin m) (Fin n) ℂ →ₗ[ℂ] ℂ)
    (W : Submodule ℂ (Matrix (Fin m) (Fin n) ℂ))
    (hW : ∀ (x : Fin m → ℂ) (y : Fin n → ℂ), φ (vecMulVec x y) = 0 → vecMulVec x y ∈ W)
    (a : Fin m → ℂ) (b : Fin n → ℂ) (hab : φ (vecMulVec a b) ≠ 0) (hE : vecMulVec a b ∈ W)
    (x : Fin m → ℂ) (y : Fin n → ℂ) : vecMulVec x y ∈ W := by
  have hA : ∀ x' : Fin m → ℂ, vecMulVec x' b ∈ W := by
    intro x'
    have h0 : vecMulVec (x' + (-(φ (vecMulVec x' b)) / φ (vecMulVec a b)) • a) b ∈ W := by
      refine hW _ _ ?_
      rw [vmv_left, map_add, map_smul, smul_eq_mul, div_mul_cancel₀ _ hab, add_neg_cancel]
    have e : vecMulVec x' b =
        vecMulVec (x' + (-(φ (vecMulVec x' b)) / φ (vecMulVec a b)) • a) b
          - (-(φ (vecMulVec x' b)) / φ (vecMulVec a b)) • vecMulVec a b := by
      rw [vmv_left]
      abel
    rw [e]
    exact W.sub_mem h0 (W.smul_mem _ hE)
  have hB : ∀ y' : Fin n → ℂ, vecMulVec a y' ∈ W := by
    intro y'
    have h0 : vecMulVec a (y' + (-(φ (vecMulVec a y')) / φ (vecMulVec a b)) • b) ∈ W := by
      refine hW _ _ ?_
      rw [vmv_right, map_add, map_smul, smul_eq_mul, div_mul_cancel₀ _ hab, add_neg_cancel]
    have e : vecMulVec a y' =
        vecMulVec a (y' + (-(φ (vecMulVec a y')) / φ (vecMulVec a b)) • b)
          - (-(φ (vecMulVec a y')) / φ (vecMulVec a b)) • vecMulVec a b := by
      rw [vmv_right]
      abel
    rw [e]
    exact W.sub_mem h0 (W.smul_mem _ hE)
  have key : ∀ s t : ℂ, vecMulVec (x + s • a) (y + t • b) =
      vecMulVec x y + t • vecMulVec x b + s • vecMulVec a y + (s * t) • vecMulVec a b := by
    intro s t
    rw [vmv_left, vmv_right, vmv_right, smul_add, smul_smul]
    abel
  obtain ⟨s, hs⟩ : ∃ s : ℂ, φ (vecMulVec x b) + s * φ (vecMulVec a b) = φ (vecMulVec a b) :=
    ⟨1 - φ (vecMulVec x b) / φ (vecMulVec a b), by
      rw [sub_mul, one_mul, div_mul_cancel₀ _ hab]
      ring⟩
  obtain ⟨t, ht⟩ : ∃ t : ℂ, t * φ (vecMulVec a b) =
      -(φ (vecMulVec x y) + s * φ (vecMulVec a y)) :=
    ⟨-(φ (vecMulVec x y) + s * φ (vecMulVec a y)) / φ (vecMulVec a b), div_mul_cancel₀ _ hab⟩
  have hG : vecMulVec (x + s • a) (y + t • b) ∈ W := by
    refine hW _ _ ?_
    rw [key, map_add, map_add, map_add, map_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
      smul_eq_mul]
    linear_combination t * hs + ht
  have e : vecMulVec x y = vecMulVec (x + s • a) (y + t • b) - t • vecMulVec x b
      - s • vecMulVec a y - (s * t) • vecMulVec a b := by
    rw [key]
    abel
  rw [e]
  exact W.sub_mem (W.sub_mem (W.sub_mem hG (W.smul_mem _ (hA x))) (W.smul_mem _ (hB y)))
    (W.smul_mem _ hE)

/-- The kernel of a nonzero functional is spanned by the rank-one matrices it contains. -/
theorem ker_le_span_r1 {m n : ℕ} (φ : Matrix (Fin m) (Fin n) ℂ →ₗ[ℂ] ℂ) (hφ : φ ≠ 0) :
    LinearMap.ker φ ≤ Submodule.span ℂ {M : Matrix (Fin m) (Fin n) ℂ |
      (∃ (a : Fin m → ℂ) (b : Fin n → ℂ), M = vecMulVec a b) ∧ φ M = 0} := by
  have hall : ∀ B : Matrix (Fin m) (Fin n) ℂ, B ∈ Submodule.span ℂ
      {M : Matrix (Fin m) (Fin n) ℂ | ∃ (a : Fin m → ℂ) (b : Fin n → ℂ), M = vecMulVec a b} := by
    intro B
    rw [span_r1_top]
    exact Submodule.mem_top
  obtain ⟨a, b, hab⟩ : ∃ (a : Fin m → ℂ) (b : Fin n → ℂ), φ (vecMulVec a b) ≠ 0 := by
    by_contra hcon
    have hcon' : ∀ (a : Fin m → ℂ) (b : Fin n → ℂ), φ (vecMulVec a b) = 0 :=
      fun a b => by_contra fun h => hcon ⟨a, b, h⟩
    refine hφ (LinearMap.ext fun A => ?_)
    have hle : Submodule.span ℂ {M : Matrix (Fin m) (Fin n) ℂ |
        ∃ (a : Fin m → ℂ) (b : Fin n → ℂ), M = vecMulVec a b} ≤ LinearMap.ker φ := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨a, b, rfl⟩
      exact LinearMap.mem_ker.mpr (hcon' a b)
    exact LinearMap.mem_ker.mp (hle (hall A))
  intro A hA
  have htop : A ∈ Submodule.span ℂ {M : Matrix (Fin m) (Fin n) ℂ |
      (∃ (a : Fin m → ℂ) (b : Fin n → ℂ), M = vecMulVec a b) ∧ φ M = 0} ⊔
        Submodule.span ℂ {vecMulVec a b} := by
    have hW : ∀ (x : Fin m → ℂ) (y : Fin n → ℂ), φ (vecMulVec x y) = 0 →
        vecMulVec x y ∈ Submodule.span ℂ {M : Matrix (Fin m) (Fin n) ℂ |
          (∃ (a : Fin m → ℂ) (b : Fin n → ℂ), M = vecMulVec a b) ∧ φ M = 0} ⊔
            Submodule.span ℂ {vecMulVec a b} :=
      fun x y h => Submodule.mem_sup_left (Submodule.subset_span ⟨⟨x, y, rfl⟩, h⟩)
    refine (Submodule.span_le.mpr ?_) (hall A)
    rintro _ ⟨x, y, rfl⟩
    exact r1_mem_of φ _ hW a b hab
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)) x y
  obtain ⟨z, hz, w, hw, hzw⟩ := Submodule.mem_sup.mp htop
  obtain ⟨k, rfl⟩ := Submodule.mem_span_singleton.mp hw
  have hle : Submodule.span ℂ {M : Matrix (Fin m) (Fin n) ℂ |
      (∃ (a : Fin m → ℂ) (b : Fin n → ℂ), M = vecMulVec a b) ∧ φ M = 0} ≤ LinearMap.ker φ :=
    Submodule.span_le.mpr fun M hM => LinearMap.mem_ker.mpr hM.2
  have hzφ : φ z = 0 := LinearMap.mem_ker.mp (hle hz)
  have hk : k = 0 := by
    have h := LinearMap.mem_ker.mp hA
    rw [← hzw, map_add, map_smul, hzφ, zero_add, smul_eq_mul] at h
    exact (mul_eq_zero.mp h).resolve_right hab
  rw [← hzw, hk, zero_smul, add_zero]
  exact hz

/-- A proper subspace of `m × n` matrices is covered by `m n - 1` rank-one matrices. -/
theorem cover_of_finrank_lt {m n : ℕ} (S : Submodule ℂ (Matrix (Fin m) (Fin n) ℂ))
    (hS : Module.finrank ℂ S < m * n) :
    ∃ (x : Fin (m * n - 1) → Fin m → ℂ) (y : Fin (m * n - 1) → Fin n → ℂ),
      S ≤ Submodule.span ℂ (Set.range fun l => vecMulVec (x l) (y l)) := by
  have hfin := finrank_matrix_eq m n
  have hlt : S < ⊤ := Submodule.lt_top_of_finrank_lt_finrank (by rw [hfin]; exact hS)
  obtain ⟨φ, hφ, hSφ⟩ := S.exists_le_ker_of_lt_top hlt
  have hker := ker_le_span_r1 φ hφ
  have hle : Submodule.span ℂ {M : Matrix (Fin m) (Fin n) ℂ |
      (∃ (a : Fin m → ℂ) (b : Fin n → ℂ), M = vecMulVec a b) ∧ φ M = 0} ≤ LinearMap.ker φ :=
    Submodule.span_le.mpr fun M hM => LinearMap.mem_ker.mpr hM.2
  have hne : Submodule.span ℂ {M : Matrix (Fin m) (Fin n) ℂ |
      (∃ (a : Fin m → ℂ) (b : Fin n → ℂ), M = vecMulVec a b) ∧ φ M = 0} ≠ ⊤ := by
    intro htop
    refine hφ (LinearMap.ext fun A => ?_)
    have hA : A ∈ Submodule.span ℂ {M : Matrix (Fin m) (Fin n) ℂ |
        (∃ (a : Fin m → ℂ) (b : Fin n → ℂ), M = vecMulVec a b) ∧ φ M = 0} := by
      rw [htop]
      exact Submodule.mem_top
    exact LinearMap.mem_ker.mp (hle hA)
  have hfr := Submodule.finrank_lt hne
  rw [hfin] at hfr
  obtain ⟨x, y, hxy⟩ := cover_of_span {M : Matrix (Fin m) (Fin n) ℂ |
      (∃ (a : Fin m → ℂ) (b : Fin n → ℂ), M = vecMulVec a b) ∧ φ M = 0}
    (fun M hM => hM.1) (r := m * n - 1) (by omega)
  exact ⟨x, y, hSφ.trans (hker.trans hxy)⟩

/-- The upper bounds on the level of slice spaces. -/
theorem upper_cover (h1 : H1) {m n u : ℕ} (hm : 3 ≤ m) (hmn : m ≤ n) (hu : u ≤ 4)
    (r : ℕ) (hr : r + (u + 1) / 2 = m * n)
    (S : Submodule ℂ (Matrix (Fin m) (Fin n) ℂ)) (hS : Module.finrank ℂ S + u ≤ m * n) :
    ∃ (x : Fin r → Fin m → ℂ) (y : Fin r → Fin n → ℂ),
      S ≤ Submodule.span ℂ (Set.range fun l => vecMulVec (x l) (y l)) := by
  have hmn9 : 9 ≤ m * n := by nlinarith
  rcases Nat.lt_or_ge u 1 with h0 | h0
  · obtain rfl : r = m * n := by omega
    have htop := span_r1_top m n
    obtain ⟨x, y, hxy⟩ := cover_of_span {M : Matrix (Fin m) (Fin n) ℂ |
        ∃ (a : Fin m → ℂ) (b : Fin n → ℂ), M = vecMulVec a b}
      (fun M hM => hM) (r := m * n) (by rw [htop, finrank_top, finrank_matrix_eq])
    refine ⟨x, y, le_trans ?_ hxy⟩
    rw [htop]
    exact le_top
  rcases Nat.lt_or_ge u 3 with h3 | h3
  · obtain rfl : r = m * n - 1 := by omega
    exact cover_of_finrank_lt S (by omega)
  · obtain rfl : r = m * n - 2 := by omega
    exact h1 m n hm hmn S (by omega)

/-- The rank bound for a tensor from the cover of all small subspaces. -/
theorem cprank_le_of_forall {m n p r : ℕ} (T : Holor ℂ [m, n, p])
    (hcov : ∀ S : Submodule ℂ (Matrix (Fin m) (Fin n) ℂ), Module.finrank ℂ S ≤ p →
      ∃ (x : Fin r → Fin m → ℂ) (y : Fin r → Fin n → ℂ),
        S ≤ Submodule.span ℂ (Set.range fun l => vecMulVec (x l) (y l))) : T.cprank ≤ r := by
  obtain ⟨x, y, hxy⟩ := hcov _ (finrank_span_range_le fun k : Fin p =>
    (Matrix.of fun (i : Fin m) (j : Fin n) =>
      T ⟨[i.1, j.1, k.1], .cons i.2 (.cons j.2 (.cons k.2 .nil))⟩ : Matrix (Fin m) (Fin n) ℂ))
  exact cprank_le_of_cover T x y fun k => hxy (Submodule.subset_span ⟨k, rfl⟩)

-- ### Lower bounds

/-- A subspace of dimension at most `p` is the span of `p` matrices. -/
theorem exists_fin_span {m n p : ℕ} (S : Submodule ℂ (Matrix (Fin m) (Fin n) ℂ))
    (hS : Module.finrank ℂ S ≤ p) :
    ∃ f : Fin p → Matrix (Fin m) (Fin n) ℂ, Submodule.span ℂ (Set.range f) = S := by
  obtain ⟨g, hg, hspan, -⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℂ (S : Set (Matrix (Fin m) (Fin n) ℂ))
  have hd : Module.finrank ℂ (Submodule.span ℂ (S : Set (Matrix (Fin m) (Fin n) ℂ))) ≤ p := by
    rw [Submodule.span_eq]
    exact hS
  refine ⟨fun l => if h : l.1 < Module.finrank ℂ
      (Submodule.span ℂ (S : Set (Matrix (Fin m) (Fin n) ℂ))) then g ⟨l.1, h⟩ else 0, ?_⟩
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨l, rfl⟩
    by_cases h : l.1 < Module.finrank ℂ (Submodule.span ℂ (S : Set (Matrix (Fin m) (Fin n) ℂ)))
    · simp only [dif_pos h]
      exact hg _
    · simp only [dif_neg h]
      exact S.zero_mem
  · refine le_trans (le_of_eq ((Submodule.span_eq S).symm.trans hspan.symm))
      (Submodule.span_mono ?_)
    rintro _ ⟨i, rfl⟩
    refine ⟨⟨i.1, lt_of_lt_of_le i.2 hd⟩, ?_⟩
    simp only [dif_pos i.2]

/-- A subspace of dimension at most `p` that is covered by no `r` rank-one matrices gives a tensor
with `p` slices of rank more than `r`. -/
theorem exists_rank_gt {m n p r : ℕ} (S : Submodule ℂ (Matrix (Fin m) (Fin n) ℂ))
    (hS : Module.finrank ℂ S ≤ p)
    (hno : ∀ (x : Fin r → Fin m → ℂ) (y : Fin r → Fin n → ℂ),
      ¬ S ≤ Submodule.span ℂ (Set.range fun l => vecMulVec (x l) (y l))) :
    ∃ T : Holor ℂ [m, n, p], r < T.cprank := by
  obtain ⟨f, hf⟩ := exists_fin_span S hS
  obtain ⟨T, hT⟩ := exists_holor f
  refine ⟨T, ?_⟩
  by_contra hlt
  obtain ⟨x, y, hxy⟩ := cover_of_cprank_le T (not_lt.mp hlt)
  refine hno x y ?_
  rw [← hf]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨k, rfl⟩
  have e : (Matrix.of fun (i : Fin m) (j : Fin n) =>
      T ⟨[i.1, j.1, k.1], .cons i.2 (.cons j.2 (.cons k.2 .nil))⟩ :
        Matrix (Fin m) (Fin n) ℂ) = f k := by
    ext i j
    exact hT i j k
  rw [← e]
  exact hxy k

theorem no_cover_top {m n r : ℕ} (hr : r < m * n) (x : Fin r → Fin m → ℂ)
    (y : Fin r → Fin n → ℂ) :
    ¬ (⊤ : Submodule ℂ (Matrix (Fin m) (Fin n) ℂ)) ≤
      Submodule.span ℂ (Set.range fun l => vecMulVec (x l) (y l)) := by
  intro hle
  have h1 := Submodule.finrank_mono hle
  have h2 := finrank_span_range_le fun l => vecMulVec (x l) (y l)
  rw [finrank_top, finrank_matrix_eq] at h1
  omega

/-- The common kernel of `u` independent functionals, each rank-one matrix of which has a
vanishing `(i₀, j₀)` entry while some element has not, is covered by no `m n - u` rank-one
matrices. -/
theorem no_cover_ker {m n u : ℕ} (i₀ : Fin m) (j₀ : Fin n)
    (f : Fin u → Matrix (Fin m) (Fin n) ℂ →ₗ[ℂ] ℂ)
    (hsurj : ∀ v : Fin u → ℂ, ∃ A : Matrix (Fin m) (Fin n) ℂ, ∀ k, f k A = v k)
    (hr1 : ∀ (x : Fin m → ℂ) (y : Fin n → ℂ),
      (∀ k, f k (vecMulVec x y) = 0) → x i₀ * y j₀ = 0)
    (A : Matrix (Fin m) (Fin n) ℂ) (hA : ∀ k, f k A = 0) (hA0 : A i₀ j₀ ≠ 0) :
    Module.finrank ℂ (LinearMap.ker (LinearMap.pi f)) + u = m * n ∧
    ∀ (x : Fin (m * n - u) → Fin m → ℂ) (y : Fin (m * n - u) → Fin n → ℂ),
      ¬ LinearMap.ker (LinearMap.pi f) ≤
        Submodule.span ℂ (Set.range fun l => vecMulVec (x l) (y l)) := by
  have hfin : Module.finrank ℂ (LinearMap.ker (LinearMap.pi f)) + u = m * n := by
    have h := LinearMap.finrank_range_add_finrank_ker (LinearMap.pi f)
    have hs : LinearMap.range (LinearMap.pi f) = ⊤ := by
      refine LinearMap.range_eq_top.mpr fun v => ?_
      obtain ⟨B, hB⟩ := hsurj v
      exact ⟨B, funext hB⟩
    rw [hs, finrank_top, finrank_matrix_eq] at h
    have h1 : Module.finrank ℂ (Fin u → ℂ) = u := Module.finrank_fin_fun ℂ
    omega
  refine ⟨hfin, fun x y hle => ?_⟩
  have hcard := finrank_span_range_le fun l => vecMulVec (x l) (y l)
  have heq := Submodule.eq_of_le_of_finrank_le hle (by omega)
  have hall : Submodule.span ℂ (Set.range fun l => vecMulVec (x l) (y l)) ≤
      LinearMap.ker (Matrix.entryLinearMap ℂ ℂ i₀ j₀) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨l, rfl⟩
    have hk : vecMulVec (x l) (y l) ∈ LinearMap.ker (LinearMap.pi f) := by
      rw [heq]
      exact Submodule.subset_span ⟨l, rfl⟩
    have h0 := LinearMap.mem_ker.mp hk
    have h := hr1 (x l) (y l) fun k => congrFun h0 k
    show vecMulVec (x l) (y l) ∈ LinearMap.ker (Matrix.entryLinearMap ℂ ℂ i₀ j₀)
    refine LinearMap.mem_ker.mpr ?_
    rw [Matrix.entryLinearMap_apply, vecMulVec_apply]
    exact h
  exact hA0 (LinearMap.mem_ker.mp (hall (hle (LinearMap.mem_ker.mpr (funext hA)))))

theorem no_cover_two {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ∃ S : Submodule ℂ (Matrix (Fin m) (Fin n) ℂ), Module.finrank ℂ S + 2 = m * n ∧
      ∀ (x : Fin (m * n - 2) → Fin m → ℂ) (y : Fin (m * n - 2) → Fin n → ℂ),
        ¬ S ≤ Submodule.span ℂ (Set.range fun l => vecMulVec (x l) (y l)) := by
  have h := no_cover_ker (⟨0, by omega⟩ : Fin m) (⟨0, by omega⟩ : Fin n)
    ![Matrix.entryLinearMap ℂ ℂ (⟨0, by omega⟩ : Fin m) (⟨0, by omega⟩ : Fin n) +
        Matrix.entryLinearMap ℂ ℂ (⟨1, by omega⟩ : Fin m) (⟨1, by omega⟩ : Fin n),
      Matrix.entryLinearMap ℂ ℂ (⟨0, by omega⟩ : Fin m) (⟨1, by omega⟩ : Fin n)]
    ?_ ?_
    (Matrix.of fun i j => if i.1 = 0 ∧ j.1 = 0 then 1 else if i.1 = 1 ∧ j.1 = 1 then -1 else 0)
    ?_ ?_
  · exact ⟨_, h⟩
  · intro v
    refine ⟨Matrix.of fun i j => if i.1 = 0 ∧ j.1 = 0 then v 0
      else if i.1 = 0 ∧ j.1 = 1 then v 1 else 0, fun k => ?_⟩
    fin_cases k <;> simp
  · intro x y h
    have h0 : x ⟨0, by omega⟩ * y ⟨0, by omega⟩ + x ⟨1, by omega⟩ * y ⟨1, by omega⟩ = 0 := h 0
    have h1 : x ⟨0, by omega⟩ * y ⟨1, by omega⟩ = 0 := h 1
    refine mul_self_eq_zero.mp ?_
    linear_combination (x ⟨0, by omega⟩ * y ⟨0, by omega⟩) * h0
      - (x ⟨1, by omega⟩ * y ⟨0, by omega⟩) * h1
  · intro k
    fin_cases k <;> simp
  · simp

theorem no_cover_three {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n) :
    ∃ S : Submodule ℂ (Matrix (Fin m) (Fin n) ℂ), Module.finrank ℂ S + 3 = m * n ∧
      ∀ (x : Fin (m * n - 3) → Fin m → ℂ) (y : Fin (m * n - 3) → Fin n → ℂ),
        ¬ S ≤ Submodule.span ℂ (Set.range fun l => vecMulVec (x l) (y l)) := by
  have h := no_cover_ker (⟨0, by omega⟩ : Fin m) (⟨0, by omega⟩ : Fin n)
    ![Matrix.entryLinearMap ℂ ℂ (⟨0, by omega⟩ : Fin m) (⟨0, by omega⟩ : Fin n) +
        Matrix.entryLinearMap ℂ ℂ (⟨1, by omega⟩ : Fin m) (⟨1, by omega⟩ : Fin n),
      Matrix.entryLinearMap ℂ ℂ (⟨0, by omega⟩ : Fin m) (⟨1, by omega⟩ : Fin n),
      Matrix.entryLinearMap ℂ ℂ (⟨2, by omega⟩ : Fin m) (⟨2, by omega⟩ : Fin n)]
    ?_ ?_
    (Matrix.of fun i j => if i.1 = 0 ∧ j.1 = 0 then 1 else if i.1 = 1 ∧ j.1 = 1 then -1 else 0)
    ?_ ?_
  · exact ⟨_, h⟩
  · intro v
    refine ⟨Matrix.of fun i j => if i.1 = 0 ∧ j.1 = 0 then v 0
      else if i.1 = 0 ∧ j.1 = 1 then v 1 else if i.1 = 2 ∧ j.1 = 2 then v 2 else 0, fun k => ?_⟩
    fin_cases k <;> simp
  · intro x y h
    have h0 : x ⟨0, by omega⟩ * y ⟨0, by omega⟩ + x ⟨1, by omega⟩ * y ⟨1, by omega⟩ = 0 := h 0
    have h1 : x ⟨0, by omega⟩ * y ⟨1, by omega⟩ = 0 := h 1
    refine mul_self_eq_zero.mp ?_
    linear_combination (x ⟨0, by omega⟩ * y ⟨0, by omega⟩) * h0
      - (x ⟨1, by omega⟩ * y ⟨0, by omega⟩) * h1
  · intro k
    fin_cases k <;> simp
  · simp

/-- The lower bounds on the level of slice spaces. -/
theorem lower_nocover (h2 : H2) {m n u : ℕ} (hm : 3 ≤ m) (hmn : m ≤ n) (hu : u ≤ 4)
    (hum : u ≤ m) (r : ℕ) (hr : r + (u + 1) / 2 + 1 = m * n) :
    ∃ S : Submodule ℂ (Matrix (Fin m) (Fin n) ℂ), Module.finrank ℂ S + u ≤ m * n ∧
      ∀ (x : Fin r → Fin m → ℂ) (y : Fin r → Fin n → ℂ),
        ¬ S ≤ Submodule.span ℂ (Set.range fun l => vecMulVec (x l) (y l)) := by
  have hmn9 : 9 ≤ m * n := by nlinarith
  rcases Nat.lt_or_ge u 1 with h0 | h0
  · refine ⟨⊤, ?_, fun x y => no_cover_top (by omega) x y⟩
    rw [finrank_top, finrank_matrix_eq]
    omega
  rcases Nat.lt_or_ge u 3 with h3 | h3
  · obtain ⟨S, hS, hno⟩ := no_cover_two (m := m) (n := n) (by omega) (by omega)
    obtain rfl : r = m * n - 2 := by omega
    exact ⟨S, by omega, hno⟩
  rcases Nat.lt_or_ge u 4 with h4 | h4
  · obtain ⟨S, hS, hno⟩ := no_cover_three (m := m) (n := n) hm (by omega)
    obtain rfl : r = m * n - 3 := by omega
    exact ⟨S, by omega, hno⟩
  · obtain ⟨S, hS, hno⟩ := h2 m n (by omega) hmn
    obtain rfl : r = m * n - 3 := by omega
    exact ⟨S, by omega, hno⟩

theorem main : H1 → H2 → type_of% @Arxiv.«0805.3777».isMaxRank_of_le_min := by
  intro h1 h2 m n u hm hmn hu
  have hu4 : u ≤ 4 := le_trans hu (min_le_left _ _)
  have hum : u ≤ m := le_trans hu (min_le_right _ _)
  have hmn9 : 9 ≤ m * n := by nlinarith
  have hc : u ⌈/⌉ 2 = (u + 2 - 1) / 2 := Nat.ceilDiv_eq_add_pred_div u 2
  have hup : ∀ T : Holor ℂ [m, n, m * n - u], T.cprank ≤ m * n - u ⌈/⌉ 2 := fun T =>
    cprank_le_of_forall T fun S hS =>
      upper_cover h1 hm hmn hu4 (m * n - u ⌈/⌉ 2) (by omega) S (by omega)
  obtain ⟨S, hS, hno⟩ := lower_nocover h2 hm hmn hu4 hum (m * n - u ⌈/⌉ 2 - 1) (by omega)
  obtain ⟨T, hT⟩ := exists_rank_gt S (p := m * n - u) (by omega) hno
  refine ⟨⟨T, ?_⟩, ?_⟩
  · have hle := hup T
    show T.cprank = m * n - u ⌈/⌉ 2
    omega
  · rintro r ⟨T', rfl⟩
    exact hup T'

end OMA.R_Arxiv_0805_3777_isMaxRank_of_le_min_R1
