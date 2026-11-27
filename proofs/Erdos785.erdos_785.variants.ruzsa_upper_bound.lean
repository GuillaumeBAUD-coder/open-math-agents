import FormalConjectures.ErdosProblems.«785»
import Mathlib.Data.Nat.Prime.Factorial

/-!
Ruzsa, Exact additive complements, Theorem 1.3.
The counting estimates adapt the public Danzer proof in open-math-agents PR 2119
by @OrangeHeadz. Complete residue systems at selected stages let the denominator
match the sparse set count at arbitrarily large cutoffs.
-/

namespace Ruzsa785

open Filter Finset
open scoped Pointwise

structure Prefix (w : ℕ → ℝ) where
  len : ℕ
  av : ℕ → ℕ
  zero : av 0 = 0
  growth : ∀ i < len, av i < av (i + 1) ∧ (i + 1)^3 * av i ≤ av (i + 1) ∧
    ((i * (i + 1) * av i : ℕ) : ℝ) < w (av (i + 1) - 1)
  lattice : ∀ i ≤ len, av i ≡ i [MOD (i^2).factorial]
  complete : 0 < len → ∀ n, ∃ i, 1 ≤ i ∧ i ≤ len ∧ av i ≡ n [MOD len]

private lemma prefix_lt {w : ℕ → ℝ} (D : Prefix w) {i j : ℕ} (hij : i < j)
    (hj : j ≤ D.len) : D.av i < D.av j := by
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.eq_or_lt_of_le (show i ≤ j by omega) with rfl | h
    · exact (D.growth i hj).1
    · exact (ih h (by omega)).trans (D.growth j hj).1

private lemma arithmetic_choice (w : ℕ → ℝ) (hw : Tendsto w atTop atTop)
    {p d a b : ℕ} (hp : 0 < p) (hd : 0 < d)
    (h : ∃ x, x ≡ a [MOD d] ∧ x ≡ b [MOD p]) (i v : ℕ) :
    ∃ x, v < x ∧ (i + 1)^3 * v ≤ x ∧
      ((i * (i + 1) * v : ℕ) : ℝ) < w (x - 1) ∧ x ≡ a [MOD d] ∧ x ≡ b [MOD p] := by
  obtain ⟨u, hda, hpb⟩ := h
  obtain ⟨L, hL⟩ := eventually_atTop.mp (hw.eventually_gt_atTop ((i * (i+1) * v : ℕ) : ℝ))
  let t := L + v + (i + 1)^3 * v + 1
  let x := u + d * p * t
  have hxt : t ≤ x := by
    have hmul : t ≤ d * p * t := Nat.le_mul_of_pos_left t (Nat.mul_pos hd hp)
    dsimp [x]
    omega
  have hdx : d ∣ d * p * t := ⟨p * t, by ring⟩
  have hpx : p ∣ d * p * t := ⟨d * t, by ring⟩
  refine ⟨x, by dsimp [t] at hxt; omega, by dsimp [t] at hxt; omega, hL _ ?_, ?_, ?_⟩
  · dsimp [t] at hxt
    omega
  · simpa [x] using hda.add (Nat.modEq_zero_iff_dvd.mpr hdx)
  · simpa [x] using hpb.add (Nat.modEq_zero_iff_dvd.mpr hpx)

private lemma extend_prefix {w : ℕ → ℝ} (hw : Tendsto w atTop atTop) (D : Prefix w) :
    ∃ E : Prefix w, D.len < E.len ∧ ∀ i ≤ D.len, E.av i = D.av i := by
  classical
  let M := max D.len (D.av D.len)
  have hKM : D.len ≤ M := le_max_left _ _
  have hAM : D.av D.len ≤ M := le_max_right _ _
  obtain ⟨p, hpB, hp⟩ := Nat.exists_infinite_primes (M ^ 2 + M + 2)
  have hpM : M < p := by omega
  have hpS : M ^ 2 < p := by omega
  let old := (Icc 1 D.len).image D.av
  have hold : old ⊆ Icc 1 M := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    obtain ⟨hi1, hik⟩ := mem_Icc.mp hi
    have hiP := prefix_lt D (show 0 < i by omega) hik
    rw [D.zero] at hiP
    have hle : D.av i ≤ D.av D.len := by
      rcases Nat.eq_or_lt_of_le hik with rfl | h
      · rfl
      · exact (prefix_lt D h le_rfl).le
    exact mem_Icc.mpr ⟨hiP, hle.trans hAM⟩
  have hcard : old.card = D.len := by
    change ((Icc 1 D.len).image D.av).card = _
    rw [card_image_of_injOn (f := D.av)]
    · rw [Nat.card_Icc]; omega
    · intro i hi j hj he
      have hi' := (mem_Icc.mp (show i ∈ Icc 1 D.len from hi)).2
      have hj' := (mem_Icc.mp (show j ∈ Icc 1 D.len from hj)).2
      rcases lt_trichotomy i j with h | rfl | h
      · exact False.elim ((prefix_lt D h hj').ne he)
      · rfl
      · exact False.elim ((prefix_lt D h hi').ne he.symm)
  let missing := Icc 1 M \ old
  let new := Ioc D.len M
  have hec : new.card = missing.card := by
    dsimp [new, missing]
    rw [card_sdiff_of_subset hold, Nat.card_Ioc, Nat.card_Icc, hcard]
    omega
  let e := Finset.equivOfCardEq hec
  let r (i : ℕ) := if h : i ∈ new then (e ⟨i,h⟩ : ℕ) else i
  have hr (i : ℕ) (h : i ∈ new) : r i ∈ missing := by
    simp only [r, dif_pos h]
    exact (e ⟨i,h⟩).property
  have hwitness (i v : ℕ) (hi : D.len < i + 1) :
      ∃ x, v < x ∧ (i + 1)^3 * v ≤ x ∧
        ((i * (i + 1) * v : ℕ) : ℝ) < w (x - 1) ∧
        x ≡ i + 1 [MOD ((i + 1)^2).factorial] ∧ x ≡ r (i + 1) [MOD p] := by
    apply arithmetic_choice w hw hp.pos (Nat.factorial_pos _) _ i v
    by_cases hm : i + 1 ≤ M
    · have hcp := hp.coprime_factorial_of_lt ((Nat.pow_le_pow_left hm 2).trans_lt hpS)
      exact ⟨Nat.chineseRemainder hcp.symm (i + 1) (r (i + 1)),
        (Nat.chineseRemainder hcp.symm (i + 1) (r (i + 1))).property⟩
    · have hn : i + 1 ∉ new := by
        intro h
        exact hm (mem_Ioc.mp (show i + 1 ∈ Ioc D.len M from h)).2
      exact ⟨i + 1, Nat.ModEq.refl _, by simp only [r, dif_neg hn]; rfl⟩
  let b : ℕ → ℕ := Nat.rec (D.av 0) fun i v =>
    if hi : D.len < i + 1 then (hwitness i v hi).choose else D.av (i + 1)
  have hb (i : ℕ) (hi : i ≤ D.len) : b i = D.av i := by
    cases i with
    | zero => rfl
    | succ i =>
      change (if hi' : D.len < i + 1 then (hwitness i (b i) hi').choose else D.av (i+1)) = _
      rw [dif_neg (by omega)]
  have hstep (i : ℕ) (hi : D.len < i + 1) :
      b i < b (i + 1) ∧ (i+1)^3*b i ≤ b (i+1) ∧
        ((i*(i+1)*b i : ℕ) : ℝ) < w (b (i+1)-1) ∧
        b (i+1) ≡ i+1 [MOD ((i+1)^2).factorial] ∧ b (i+1) ≡ r (i+1) [MOD p] := by
    have heq : b (i+1) = (hwitness i (b i) hi).choose := by
      change (if h : D.len < i + 1 then (hwitness i (b i) h).choose else D.av (i+1)) = _
      rw [dif_pos hi]
    rw [heq]
    exact (hwitness i (b i) hi).choose_spec
  have hlen : D.len < p := hKM.trans_lt hpM
  refine ⟨⟨p,b, D.zero, ?_, ?_, ?_⟩, hlen, hb⟩
  · intro i hi
    by_cases hk : D.len < i + 1
    · exact ⟨(hstep i hk).1, (hstep i hk).2.1, (hstep i hk).2.2.1⟩
    · rw [hb i (by omega), hb (i+1) (by omega)]
      exact D.growth i (by omega)
  · intro i _
    by_cases hik : i ≤ D.len
    · rw [hb i hik]
      exact D.lattice i hik
    · obtain ⟨j,rfl⟩ : ∃ j, i = j+1 := ⟨i-1,by omega⟩
      exact (hstep j (by omega)).2.2.2.1
  · intro _ n
    let z := if n % p = 0 then p else n % p
    have hz1 : 1 ≤ z := by
      dsimp [z]
      split <;> omega
    have hzp : z ≤ p := by
      dsimp [z]
      split
      · rfl
      · exact (Nat.mod_lt _ hp.pos).le
    have hn : z ≡ n [MOD p] := by
      change z % p = n % p
      dsimp [z]
      split <;> simp_all
    by_cases hzM : z ≤ M
    · by_cases hzOld : z ∈ old
      · obtain ⟨i, hi, heq⟩ := mem_image.mp hzOld
        have hi' := mem_Icc.mp hi
        refine ⟨i, hi'.1, hi'.2.trans (by omega), ?_⟩
        rwa [(hb i hi'.2).trans heq]
      · have hzMissing : z ∈ missing := mem_sdiff.mpr ⟨mem_Icc.mpr ⟨hz1,hzM⟩,hzOld⟩
        obtain ⟨u, hu⟩ := e.surjective ⟨z,hzMissing⟩
        let i := u.val
        have hi := mem_Ioc.mp (show i ∈ Ioc D.len M from u.property)
        have her : r i = z := by
          simp only [r, dif_pos (show i ∈ new from u.property)]
          exact congrArg Subtype.val hu
        obtain ⟨j, hj⟩ : ∃ j, i = j+1 := ⟨i-1,by omega⟩
        have h := (hstep j (by omega)).2.2.2.2
        rw [← hj, her] at h
        exact ⟨i, by omega, by omega, h.trans hn⟩
    · have hnot : z ∉ new := by
        intro h
        exact hzM (mem_Ioc.mp (show z ∈ Ioc D.len M from h)).2
      have her : r z = z := by simp [r, hnot]
      obtain ⟨j, hj⟩ : ∃ j, z = j+1 := ⟨z-1,by omega⟩
      have h := (hstep j (by omega)).2.2.2.2
      rw [← hj, her] at h
      exact ⟨z,hz1,hzp,h.trans hn⟩

structure Ladder (w : ℕ → ℝ) where
  av : ℕ → ℕ
  zero : av 0 = 0
  growth : ∀ i, av i < av (i + 1) ∧ (i + 1)^3 * av i ≤ av (i + 1) ∧
    ((i * (i + 1) * av i : ℕ) : ℝ) < w (av (i + 1) - 1)
  lattice : ∀ i, av i ≡ i [MOD (i^2).factorial]
  complete : ∀ N : ℕ, ∃ k ≥ N, ∀ n, ∃ i, 1 ≤ i ∧ i ≤ k ∧ av i ≡ n [MOD k]

private lemma make_ladder (w : ℕ → ℝ) (hw : Tendsto w atTop atTop) : Nonempty (Ladder w) := by
  classical
  let start : Prefix w := {
    len := 0
    av := fun _ => 0
    zero := rfl
    growth := by omega
    lattice := by
      intro i hi
      have he : i = 0 := by omega
      subst i
      rfl
    complete := by omega }
  let P : ℕ → Prefix w := Nat.rec start fun _ D => (extend_prefix hw D).choose
  have hlen (t : ℕ) : (P t).len < (P (t+1)).len := (extend_prefix hw (P t)).choose_spec.1
  have hs : StrictMono fun t => (P t).len := strictMono_nat_of_lt_succ hlen
  have hkeep (t i : ℕ) (hi : i ≤ (P t).len) : (P (t+1)).av i = (P t).av i :=
    (extend_prefix hw (P t)).choose_spec.2 i hi
  have hstable {t u i : ℕ} (htu : t ≤ u) (hi : i ≤ (P t).len) :
      (P u).av i = (P t).av i := by
    induction u, htu using Nat.le_induction with
    | base => rfl
    | succ u hu ih => exact (hkeep u i (hi.trans (hs.monotone hu))).trans ih
  let a (i : ℕ) := (P i).av i
  have ha (i t : ℕ) (ht : i ≤ (P t).len) : a i = (P t).av i := by
    rcases le_total i t with hit | hti
    · exact (hstable hit (hs.id_le i)).symm
    · exact hstable hti ht
  refine ⟨⟨a, (P 0).zero, ?_, fun i => (P i).lattice i (hs.id_le i), ?_⟩⟩
  · intro i
    have h : i + 1 ≤ (P (i + 1)).len := hs.id_le (i + 1)
    rw [ha i (i+1) (by omega), ha (i+1) (i+1) h]
    exact (P (i+1)).growth i (by omega)
  · intro N
    have h : N + 1 ≤ (P (N + 1)).len := hs.id_le (N + 1)
    refine ⟨(P (N+1)).len, (by omega), ?_⟩
    intro n
    obtain ⟨i, hi1, hi2, hmod⟩ := (P (N+1)).complete (by omega) n
    exact ⟨i,hi1,hi2, by rwa [ha i (N+1) hi2]⟩

end Ruzsa785

namespace Ruzsa785.Ladder

open Filter Finset
open scoped Pointwise

variable {w : ℕ → ℝ} (D : Ladder w)

def Complete (k : ℕ) : Prop :=
  ∀ n, ∃ i, 1 ≤ i ∧ i ≤ k ∧ D.av i ≡ n [MOD k]

noncomputable def lastComplete (k : ℕ) : ℕ :=
  open scoped Classical in Nat.findGreatest D.Complete k

noncomputable def md (k : ℕ) : ℕ := max (k - Nat.sqrt k) (D.lastComplete k)

def X (k : ℕ) : ℕ := k * D.av k

def Y (k : ℕ) : ℕ := (k + 1) * D.av k

def Bset : Set ℕ := {b | ∃ k, 4 ≤ k ∧ D.md k ∣ b ∧ D.X k ≤ b ∧ b < D.Y (k + 1)}

def Aset : Set ℕ := Set.range fun i : ℕ => D.av (i + 1)

lemma av_lt_succ (i : ℕ) : D.av i < D.av (i + 1) := (D.growth i).1

lemma av_strictMono : StrictMono D.av := strictMono_nat_of_lt_succ D.av_lt_succ

lemma le_av (i : ℕ) : i ≤ D.av i := D.av_strictMono.id_le i

lemma av_pos {i : ℕ} (hi : 0 < i) : 0 < D.av i := hi.trans_le (D.le_av i)

lemma av_growth (i : ℕ) (_ : 1 ≤ i) : (i+1)^3 * D.av i ≤ D.av (i+1) :=
  (D.growth i).2.1

lemma last_le (k : ℕ) : D.lastComplete k ≤ k := by
  classical
  exact Nat.findGreatest_le _

lemma md_lower (k : ℕ) : k - Nat.sqrt k ≤ D.md k := le_max_left _ _

lemma md_pos {k : ℕ} (hk : 2 ≤ k) : 0 < D.md k := by
  have h := Nat.sqrt_lt_self (show 1 < k by omega)
  exact (show 0 < k - Nat.sqrt k by omega).trans_le (D.md_lower k)

lemma md_le (k : ℕ) : D.md k ≤ k := max_le (Nat.sub_le _ _) (D.last_le k)

lemma md_le_succ (k : ℕ) : D.md k ≤ D.md (k+1) := by
  classical
  apply max_le_max
  · have h1 : Nat.sqrt (k + 1) ≤ Nat.sqrt k + 1 := Nat.sqrt_succ_le_succ_sqrt k
    have h2 := Nat.sqrt_le_self k
    have h3 := Nat.sqrt_le_self (k+1)
    omega
  · unfold lastComplete
    exact Nat.findGreatest_mono_right _ (Nat.le_succ _)

lemma md_of_complete {k : ℕ} (hk : D.Complete k) : D.md k = k := by
  classical
  have h : k ≤ D.lastComplete k := Nat.le_findGreatest le_rfl hk
  exact le_antisymm (D.md_le k) (h.trans (le_max_right _ _))

lemma cover_md {k : ℕ} (hk : 4 ≤ k) (n : ℕ) (hkn : k ≤ n) :
    ∃ i, 1 ≤ i ∧ i ≤ k ∧ D.av i ≡ n [MOD D.md k] := by
  classical
  rcases le_total (D.lastComplete k) (k - Nat.sqrt k) with h | h
  · have heq : D.md k = k - Nat.sqrt k := max_eq_left h
    let s := Nat.sqrt k
    let r := (n - (s + 1)) % D.md k
    let i := s + 1 + r
    have hs : s < k := Nat.sqrt_lt_self (by omega)
    have hm := D.md_pos (by omega : 2 ≤ k)
    have hr : r < D.md k := Nat.mod_lt _ hm
    have his : s + 1 ≤ i := by dsimp [i]; omega
    have hik : i ≤ k := by dsimp [i]; change D.md k = k - s at heq; omega
    have hs2 : k < (s + 1)^2 := Nat.lt_succ_sqrt' k
    have hi2 : (s + 1)^2 ≤ i^2 := Nat.pow_le_pow_left his 2
    have hdiv : D.md k ∣ (i^2).factorial :=
      Nat.dvd_factorial hm ((D.md_le k).trans ((Nat.le_of_lt hs2).trans hi2))
    have hc : n - (s+1) ≡ r [MOD D.md k] := (Nat.mod_modEq _ _).symm
    have hci : n ≡ i [MOD D.md k] := by
      have hh := (Nat.ModEq.refl (s+1) : s+1 ≡ s+1 [MOD D.md k]).add hc
      change s+1+(n-(s+1)) ≡ i [MOD D.md k] at hh
      rwa [Nat.add_sub_of_le (by omega)] at hh
    exact ⟨i, by omega, hik, ((D.lattice i).of_dvd hdiv).trans hci.symm⟩
  · have heq : D.md k = D.lastComplete k := max_eq_right h
    have hlast : D.lastComplete k ≠ 0 := by
      rw [← heq]; exact (D.md_pos (by omega : 2 ≤ k)).ne'
    have hc : D.Complete (D.lastComplete k) := Nat.findGreatest_of_ne_zero rfl hlast
    obtain ⟨i, h1, h2, h3⟩ := hc n
    exact ⟨i, h1, h2.trans (D.last_le k), by rwa [heq]⟩

lemma Y_eq (k : ℕ) : D.Y k = D.X k + D.av k := by unfold X Y; ring

lemma X_lt_succ (k : ℕ) : D.X k < D.X (k + 1) := by
  unfold X
  have h1 := (D.av_lt_succ k).le
  have h2 := D.av_pos (show 0 < k + 1 by omega)
  calc k * D.av k ≤ k * D.av (k + 1) := Nat.mul_le_mul_left _ h1
    _ < k * D.av (k + 1) + D.av (k + 1) := by omega
    _ = (k + 1) * D.av (k + 1) := by ring

lemma X_strictMono : StrictMono D.X := strictMono_nat_of_lt_succ D.X_lt_succ

lemma Y_le_X_succ (k : ℕ) : D.Y k ≤ D.X (k + 1) := by
  unfold X Y
  exact Nat.mul_le_mul_left _ (D.av_lt_succ k).le

lemma Y_lt_succ (k : ℕ) : D.Y k < D.Y (k + 1) := by
  have h1 := D.Y_le_X_succ k
  have h2 := D.Y_eq (k + 1)
  have h3 := D.av_pos (show 0 < k + 1 by omega)
  omega

lemma Y_strictMono : StrictMono D.Y := strictMono_nat_of_lt_succ D.Y_lt_succ

lemma le_X (k : ℕ) : k ≤ D.X k := by
  by_cases hk : k = 0
  · simp [hk]
  unfold X
  exact Nat.le_mul_of_pos_right _ (D.av_pos (by omega : 0 < k))

lemma stage (f : ℕ → ℕ) (hf : StrictMono f) {K x : ℕ} (hx : f K ≤ x) :
    ∃ k, K ≤ k ∧ f k ≤ x ∧ x < f (k + 1) := by
  have hid : ∀ n, n ≤ f n := hf.id_le
  have hKx : K ≤ x := (hid K).trans hx
  refine ⟨Nat.findGreatest (fun j => f j ≤ x) x, Nat.le_findGreatest hKx hx,
    Nat.findGreatest_spec (P := fun j => f j ≤ x) hKx hx, ?_⟩
  by_contra hcon
  have h1 : f (Nat.findGreatest (fun j => f j ≤ x) x + 1) ≤ x := Nat.le_of_not_lt hcon
  have h2 : Nat.findGreatest (fun j => f j ≤ x) x + 1 ≤ x := (hid _).trans h1
  have h3 := Nat.le_findGreatest (P := fun j => f j ≤ x) h2 h1
  omega

/-- Counting multiples of `m` in `(L, U]`. -/

lemma card_mul (m L U : ℕ) (hLU : L ≤ U) :
    ((Finset.Ioc L U).filter (fun b => m ∣ b)).card + L / m = U / m := by
  have h1 := Nat.Ioc_filter_dvd_card_eq_div U m
  have h2 := Nat.Ioc_filter_dvd_card_eq_div L m
  have hunion : (Finset.Ioc 0 U).filter (fun b => m ∣ b) =
      (Finset.Ioc 0 L).filter (fun b => m ∣ b) ∪ (Finset.Ioc L U).filter (fun b => m ∣ b) := by
    rw [← Finset.filter_union, Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le L) hLU]
  have hdisj : Disjoint ((Finset.Ioc 0 L).filter (fun b => m ∣ b))
      ((Finset.Ioc L U).filter (fun b => m ∣ b)) := by
    rw [Finset.disjoint_left]
    intro b hb1 hb2
    rw [Finset.mem_filter, Finset.mem_Ioc] at hb1 hb2
    omega
  rw [hunion, Finset.card_union_of_disjoint hdisj, h2] at h1
  omega

lemma countA_bounds {k x : ℕ} (hk : 1 ≤ k) (h1 : D.X k ≤ x) (h2 : x < D.X (k + 1)) :
    k ≤ (D.Aset ∩ Set.Icc 1 x).ncard ∧ (D.Aset ∩ Set.Icc 1 x).ncard ≤ k + 1 := by
  constructor
  · have hsub : (((Finset.Icc 1 k).image D.av : Finset ℕ) : Set ℕ) ⊆ D.Aset ∩ Set.Icc 1 x := by
      intro b hb
      rw [Finset.mem_coe, Finset.mem_image] at hb
      obtain ⟨i, hi, rfl⟩ := hb
      rw [Finset.mem_Icc] at hi
      refine ⟨⟨i - 1, ?_⟩, D.av_pos (by omega : 0 < i), ?_⟩
      · show D.av (i - 1 + 1) = D.av i
        rw [Nat.sub_add_cancel hi.1]
      · have h3 : D.av i ≤ D.av k := D.av_strictMono.monotone hi.2
        have h4 : D.av k ≤ D.X k := by
          unfold X
          exact Nat.le_mul_of_pos_left _ (by omega)
        omega
    have hfin : (D.Aset ∩ Set.Icc 1 x).Finite := (Set.finite_Icc 1 x).inter_of_right _
    have h := Set.ncard_le_ncard hsub hfin
    rw [Set.ncard_coe_finset, Finset.card_image_of_injective _ D.av_strictMono.injective,
      Nat.card_Icc] at h
    omega
  · have hsub : D.Aset ∩ Set.Icc 1 x ⊆ (((Finset.Icc 1 (k + 1)).image D.av : Finset ℕ) : Set ℕ) := by
      rintro b ⟨⟨i, rfl⟩, -, hbx⟩
      rw [Finset.mem_coe, Finset.mem_image]
      refine ⟨i + 1, ?_, rfl⟩
      rw [Finset.mem_Icc]
      refine ⟨by omega, ?_⟩
      by_contra hcon
      have h3 : D.av (k + 1 + 1) ≤ D.av (i + 1) := D.av_strictMono.monotone (by omega)
      have h4 := D.av_growth (k + 1) (by omega)
      have h5 : (k + 1) * D.av (k + 1) < (k + 1 + 1) ^ 3 * D.av (k + 1) := by
        apply Nat.mul_lt_mul_of_pos_right _ (D.av_pos (by omega : 0 < k + 1))
        calc k + 1 < k + 1 + 1 := by omega
          _ ≤ (k + 1 + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
      have h6 : D.X (k + 1) = (k + 1) * D.av (k + 1) := rfl
      simp only [] at hbx
      omega
    have h := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset] at h
    have h' := Finset.card_image_le (s := Finset.Icc 1 (k + 1)) (f := D.av)
    rw [Nat.card_Icc] at h'
    omega

lemma countB_upper {j x : ℕ} (hj : 4 ≤ j) (h1 : D.X (j + 1) ≤ x) (h2 : x < D.X (j + 2)) :
    D.md j * (D.Bset ∩ Set.Icc 1 x).ncard ≤ D.md j * D.Y j + x + D.av (j + 1) + D.md (j + 1) := by
  obtain ⟨F1, hF1⟩ : ∃ F : Finset ℕ, F = Finset.Ioc 0 (D.Y j) := ⟨_, rfl⟩
  obtain ⟨F2, hF2⟩ : ∃ F : Finset ℕ, F = (Finset.Ioc 0 (D.Y (j + 1))).filter (fun b => D.md j ∣ b) :=
    ⟨_, rfl⟩
  obtain ⟨F3, hF3⟩ : ∃ F : Finset ℕ,
      F = (Finset.Ioc (D.X (j + 1) - 1) x).filter (fun b => D.md (j + 1) ∣ b) := ⟨_, rfl⟩
  have hXpos : 0 < D.X (j + 1) := lt_of_lt_of_le (by omega) (D.le_X (j + 1))
  have hsub : D.Bset ∩ Set.Icc 1 x ⊆ ((F1 ∪ F2 ∪ F3 : Finset ℕ) : Set ℕ) := by
    rintro b ⟨⟨i, hi4, hdvd, hXi, hYi⟩, hb1, hbx⟩
    have hilt : i < j + 2 := D.X_strictMono.lt_iff_lt.1 (by omega)
    rw [Finset.mem_coe, Finset.mem_union, Finset.mem_union]
    rcases Nat.lt_or_ge i j with hij | hij
    · left; left
      rw [hF1, Finset.mem_Ioc]
      have h3 : D.Y (i + 1) ≤ D.Y j := D.Y_strictMono.monotone (by omega)
      exact ⟨hb1, by omega⟩
    · rcases Nat.eq_or_lt_of_le hij with rfl | hij'
      · left; right
        rw [hF2, Finset.mem_filter, Finset.mem_Ioc]
        exact ⟨⟨hb1, hYi.le⟩, hdvd⟩
      · have hi : i = j + 1 := by omega
        subst hi
        right
        rw [hF3, Finset.mem_filter, Finset.mem_Ioc]
        exact ⟨⟨by omega, hbx⟩, hdvd⟩
  have hc := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset] at hc
  have hc1 : (F1 ∪ F2 ∪ F3).card ≤ F1.card + F2.card + F3.card :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)
  have hcard1 : F1.card = D.Y j := by rw [hF1, Nat.card_Ioc]; omega
  have hcard2 : F2.card = D.Y (j + 1) / D.md j := by
    rw [hF2]; exact Nat.Ioc_filter_dvd_card_eq_div _ _
  have hcard3 : F3.card + (D.X (j + 1) - 1) / D.md (j + 1) = x / D.md (j + 1) := by
    rw [hF3]; exact card_mul _ _ _ (by omega)
  have hm' : 0 < D.md j := D.md_pos (by omega)
  have hm : 0 < D.md (j + 1) := D.md_pos (by omega)
  have hmm : D.md j ≤ D.md (j + 1) := D.md_le_succ j
  obtain ⟨c, hcdef⟩ : ∃ c, c = (D.Bset ∩ Set.Icc 1 x).ncard := ⟨_, rfl⟩
  rw [← hcdef] at hc ⊢
  obtain ⟨q1, hq1⟩ : ∃ q, q = D.Y (j + 1) / D.md j := ⟨_, rfl⟩
  obtain ⟨q2, hq2⟩ : ∃ q, q = x / D.md (j + 1) := ⟨_, rfl⟩
  obtain ⟨q3, hq3⟩ : ∃ q, q = (D.X (j + 1) - 1) / D.md (j + 1) := ⟨_, rfl⟩
  rw [← hq1] at hcard2
  rw [← hq2, ← hq3] at hcard3
  have b1 : D.md j * q1 ≤ D.Y (j + 1) := by rw [hq1]; exact Nat.mul_div_le _ _
  have b2 : D.md (j + 1) * q2 ≤ x := by rw [hq2]; exact Nat.mul_div_le _ _
  have b3 : D.X (j + 1) - 1 < D.md (j + 1) * q3 + D.md (j + 1) := by
    have := Nat.lt_mul_div_succ (D.X (j + 1) - 1) hm
    rw [← hq3] at this
    calc D.X (j + 1) - 1 < D.md (j + 1) * (q3 + 1) := this
      _ = D.md (j + 1) * q3 + D.md (j + 1) := by ring
  have e1 : D.md (j + 1) * F3.card + D.md (j + 1) * q3 = D.md (j + 1) * q2 := by
    rw [← Nat.mul_add, hcard3]
  have e2 : D.md j * F3.card ≤ D.md (j + 1) * F3.card := Nat.mul_le_mul_right _ hmm
  have e3 : D.md j * c ≤ D.md j * D.Y j + D.md j * q1 + D.md j * F3.card := by
    calc D.md j * c ≤ D.md j * (D.Y j + q1 + F3.card) := Nat.mul_le_mul_left _ (by omega)
      _ = D.md j * D.Y j + D.md j * q1 + D.md j * F3.card := by ring
  have hYeq := D.Y_eq (j + 1)
  omega

lemma countB_lower {j x : ℕ} (hj : 4 ≤ j) (h1 : D.X (j + 1) ≤ x) (h2 : x < D.X (j + 2)) :
    x ≤ D.md (j + 1) * (D.Bset ∩ Set.Icc 1 x).ncard + D.X j + 2 * D.md (j + 1) := by
  obtain ⟨G1, hG1⟩ : ∃ F : Finset ℕ,
      F = (Finset.Ioc (D.X j - 1) (D.X (j + 1) - 1)).filter (fun b => D.md j ∣ b) := ⟨_, rfl⟩
  obtain ⟨F3, hF3⟩ : ∃ F : Finset ℕ,
      F = (Finset.Ioc (D.X (j + 1) - 1) x).filter (fun b => D.md (j + 1) ∣ b) := ⟨_, rfl⟩
  have hXj : j ≤ D.X j := D.le_X j
  have hXlt : D.X j < D.X (j + 1) := D.X_lt_succ j
  have hYeq1 := D.Y_eq (j + 1)
  have hYeq2 := D.Y_eq (j + 2)
  have hsub : ((G1 ∪ F3 : Finset ℕ) : Set ℕ) ⊆ D.Bset ∩ Set.Icc 1 x := by
    intro b hb
    rw [Finset.mem_coe, Finset.mem_union] at hb
    rcases hb with hb | hb
    · rw [hG1, Finset.mem_filter, Finset.mem_Ioc] at hb
      exact ⟨⟨j, hj, hb.2, by omega, by omega⟩, by omega, by omega⟩
    · rw [hF3, Finset.mem_filter, Finset.mem_Ioc] at hb
      exact ⟨⟨j + 1, by omega, hb.2, by omega, (show b < D.Y (j + 2) by omega)⟩, by omega, hb.1.2⟩
  have hdisj : Disjoint G1 F3 := by
    rw [Finset.disjoint_left]
    intro b hb1 hb2
    rw [hG1, Finset.mem_filter, Finset.mem_Ioc] at hb1
    rw [hF3, Finset.mem_filter, Finset.mem_Ioc] at hb2
    omega
  have hfin : (D.Bset ∩ Set.Icc 1 x).Finite := (Set.finite_Icc 1 x).inter_of_right _
  have hc := Set.ncard_le_ncard hsub hfin
  rw [Set.ncard_coe_finset, Finset.card_union_of_disjoint hdisj] at hc
  have hm' : 0 < D.md j := D.md_pos (by omega)
  have hm : 0 < D.md (j + 1) := D.md_pos (by omega)
  have hmm : D.md j ≤ D.md (j + 1) := D.md_le_succ j
  obtain ⟨c, hcdef⟩ : ∃ c, c = (D.Bset ∩ Set.Icc 1 x).ncard := ⟨_, rfl⟩
  rw [← hcdef] at hc ⊢
  obtain ⟨q2, hq2⟩ : ∃ q, q = x / D.md (j + 1) := ⟨_, rfl⟩
  obtain ⟨q3, hq3⟩ : ∃ q, q = (D.X (j + 1) - 1) / D.md (j + 1) := ⟨_, rfl⟩
  obtain ⟨q4, hq4⟩ : ∃ q, q = (D.X (j + 1) - 1) / D.md j := ⟨_, rfl⟩
  obtain ⟨q5, hq5⟩ : ∃ q, q = (D.X j - 1) / D.md j := ⟨_, rfl⟩
  have hcard3 : F3.card + q3 = q2 := by
    rw [hF3, hq3, hq2]; exact card_mul _ _ _ (by omega)
  have hcard1 : G1.card + q5 = q4 := by
    rw [hG1, hq5, hq4]; exact card_mul _ _ _ (by omega)
  have b2 : x < D.md (j + 1) * q2 + D.md (j + 1) := by
    have := Nat.lt_mul_div_succ x hm
    rw [← hq2] at this
    calc x < D.md (j + 1) * (q2 + 1) := this
      _ = D.md (j + 1) * q2 + D.md (j + 1) := by ring
  have b3 : D.md (j + 1) * q3 ≤ D.X (j + 1) - 1 := by rw [hq3]; exact Nat.mul_div_le _ _
  have b4 : D.X (j + 1) - 1 < D.md j * q4 + D.md j := by
    have := Nat.lt_mul_div_succ (D.X (j + 1) - 1) hm'
    rw [← hq4] at this
    calc D.X (j + 1) - 1 < D.md j * (q4 + 1) := this
      _ = D.md j * q4 + D.md j := by ring
  have b5 : D.md j * q5 ≤ D.X j - 1 := by rw [hq5]; exact Nat.mul_div_le _ _
  have e1 : D.md (j + 1) * F3.card + D.md (j + 1) * q3 = D.md (j + 1) * q2 := by
    rw [← Nat.mul_add, hcard3]
  have e2 : D.md j * G1.card + D.md j * q5 = D.md j * q4 := by
    rw [← Nat.mul_add, hcard1]
  have e3 : D.md j * G1.card ≤ D.md (j + 1) * G1.card := Nat.mul_le_mul_right _ hmm
  have e4 : D.md (j + 1) * G1.card + D.md (j + 1) * F3.card ≤ D.md (j + 1) * c := by
    rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ hc
  omega

lemma ratio_bounds {j x T : ℕ} (hj : 4 ≤ j) (hT : (9 * T + 10) ^ 2 ≤ j)
    (h1 : D.X (j + 1) ≤ x) (h2 : x < D.X (j + 2)) :
    T * x ≤ (T + 1) * ((D.Aset ∩ Set.Icc 1 x).ncard * (D.Bset ∩ Set.Icc 1 x).ncard) ∧
      (T + 1) * ((D.Aset ∩ Set.Icc 1 x).ncard * (D.Bset ∩ Set.Icc 1 x).ncard) ≤ (T + 2) * x := by
  obtain ⟨hA1, hA2⟩ := D.countA_bounds (k := j + 1) (by omega) h1 h2
  have hU := D.countB_upper hj h1 h2
  have hL := D.countB_lower hj h1 h2
  obtain ⟨cA, hcA⟩ : ∃ c, c = (D.Aset ∩ Set.Icc 1 x).ncard := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = (D.Bset ∩ Set.Icc 1 x).ncard := ⟨_, rfl⟩
  rw [← hcA] at hA1 hA2 ⊢
  rw [← hc] at hU hL ⊢
  obtain ⟨α, hα⟩ : ∃ α, α = D.av (j + 1) := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = D.Y j := ⟨_, rfl⟩
  obtain ⟨m', hm'⟩ : ∃ m, m = D.md j := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, m = D.md (j + 1) := ⟨_, rfl⟩
  rw [← hα, ← hP, ← hm', ← hm] at hU
  rw [← hm] at hL
  have hm'pos : 0 < m' := by rw [hm']; exact D.md_pos (by omega)
  have hm'j : m' ≤ j := by rw [hm']; exact D.md_le j
  have hmj : m ≤ j + 1 := by rw [hm]; exact D.md_le (j + 1)
  have hαj : j + 1 ≤ α := by rw [hα]; exact D.le_av (j + 1)
  have hxα : (j + 1) * α ≤ x := by rw [hα]; exact h1
  have hPα : (j + 1) ^ 2 * P ≤ α := by
    have := D.av_growth j (by omega)
    rw [hP, hα]
    calc (j + 1) ^ 2 * D.Y j = (j + 1) ^ 3 * D.av j := by unfold Y; ring
      _ ≤ D.av (j + 1) := this
  have hXP : D.X j ≤ P := by
    rw [hP]; unfold X Y
    exact Nat.mul_le_mul_right _ (by omega)
  -- auxiliary products
  have p1 : (j + 1) * P ≤ α := by
    calc (j + 1) * P ≤ (j + 1) * ((j + 1) * P) :=
          Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))
      _ = (j + 1) ^ 2 * P := by ring
      _ ≤ α := hPα
  have p2 : m' * P ≤ α := (Nat.mul_le_mul_right _ (by omega)).trans p1
  have p3 : α ≤ (j + 1) * α := Nat.le_mul_of_pos_left _ (by omega)
  -- upper bound
  have hUp : m' * (cA * c) ≤ (j + 8) * x := by
    have s1 : m' * (cA * c) ≤ (j + 2) * (m' * P + x + α + m) := by
      calc m' * (cA * c) = cA * (m' * c) := by ring
        _ ≤ (j + 2) * (m' * P + x + α + m) := Nat.mul_le_mul hA2 hU
    have s2 : (j + 2) * (m' * P + α + m) ≤ 6 * x := by
      calc (j + 2) * (m' * P + α + m) ≤ (2 * (j + 1)) * (3 * α) :=
            Nat.mul_le_mul (by omega) (by omega)
        _ = 6 * ((j + 1) * α) := by ring
        _ ≤ 6 * x := Nat.mul_le_mul_left _ hxα
    calc m' * (cA * c) ≤ (j + 2) * (m' * P + x + α + m) := s1
      _ = (j + 2) * x + (j + 2) * (m' * P + α + m) := by ring
      _ ≤ (j + 2) * x + 6 * x := Nat.add_le_add_left s2 _
      _ = (j + 8) * x := by ring
  -- lower bound
  have hLo : (j + 1) * x ≤ (j + 1) * (cA * c) + 3 * x := by
    have s1 : (j + 1) * x ≤ (j + 1) * (m * c + D.X j + 2 * m) := Nat.mul_le_mul_left _ hL
    have s2 : (j + 1) * (D.X j + 2 * m) ≤ 3 * x := by
      have t1 : (j + 1) * D.X j ≤ α := (Nat.mul_le_mul_left _ hXP).trans p1
      have t2 : (j + 1) * (2 * m) ≤ 2 * ((j + 1) * α) := by
        calc (j + 1) * (2 * m) ≤ (j + 1) * (2 * α) := Nat.mul_le_mul_left _ (by omega)
          _ = 2 * ((j + 1) * α) := by ring
      have t3 : (j + 1) * (D.X j + 2 * m) = (j + 1) * D.X j + (j + 1) * (2 * m) := by ring
      omega
    have s3 : (j + 1) * (m * c) ≤ (j + 1) * (cA * c) := by
      calc (j + 1) * (m * c) = m * ((j + 1) * c) := by ring
        _ ≤ (j + 1) * (cA * c) := by
            calc m * ((j + 1) * c) ≤ (j + 1) * ((j + 1) * c) := Nat.mul_le_mul_right _ hmj
              _ ≤ (j + 1) * (cA * c) :=
                  Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hA1)
    have s4 : (j + 1) * (m * c + D.X j + 2 * m) = (j + 1) * (m * c) + (j + 1) * (D.X j + 2 * m) := by
      ring
    omega
  -- the size of `j`
  obtain ⟨s, hs⟩ : ∃ s, s = Nat.sqrt j := ⟨_, rfl⟩
  have hs1 : 9 * T + 10 ≤ s := by
    rw [hs, Nat.le_sqrt']
    exact hT
  have hs2 : s * s ≤ j := by rw [hs]; exact Nat.sqrt_le j
  have hms : j ≤ m' + s := by
    have hh := D.md_lower j
    have := Nat.sqrt_le_self j
    rw [← hm', ← hs] at hh
    rw [← hs] at this
    omega
  have hTs : T ≤ T * s := Nat.le_mul_of_pos_right _ (by omega)
  have hss : s * (9 * T + 10) ≤ s * s := Nat.mul_le_mul_left _ hs1
  have hss' : s * (9 * T + 10) = 9 * (T * s) + 10 * s := by ring
  have hbig : (s + 8) * (T + 1) ≤ m' := by
    have e : (s + 8) * (T + 1) = T * s + s + 8 * T + 8 := by ring
    omega
  have hjT : (j + 8) * (T + 1) ≤ m' * (T + 2) := by
    have e1 : (j + 8) * (T + 1) ≤ m' * (T + 1) + (s + 8) * (T + 1) := by
      calc (j + 8) * (T + 1) ≤ (m' + s + 8) * (T + 1) := Nat.mul_le_mul_right _ (by omega)
        _ = m' * (T + 1) + (s + 8) * (T + 1) := by ring
    have e2 : m' * (T + 2) = m' * (T + 1) + m' := by ring
    omega
  have hj3 : 3 * (T + 1) ≤ j + 1 := by
    have : 9 * T + 10 ≤ s * s := (Nat.le_mul_self _).trans (Nat.mul_le_mul hs1 hs1)
    omega
  constructor
  · -- lower
    have t1 : (j + 1) * (T * x) ≤ (j + 1) * ((T + 1) * (cA * c)) := by
      have u1 : (T + 1) * ((j + 1) * x) ≤ (T + 1) * ((j + 1) * (cA * c) + 3 * x) :=
        Nat.mul_le_mul_left _ hLo
      have u2 : 3 * (T + 1) * x ≤ (j + 1) * x := Nat.mul_le_mul_right _ hj3
      have u3 : (T + 1) * ((j + 1) * x) = (j + 1) * (T * x) + (j + 1) * x := by ring
      have u4 : (T + 1) * ((j + 1) * (cA * c) + 3 * x) =
          (j + 1) * ((T + 1) * (cA * c)) + 3 * (T + 1) * x := by ring
      omega
    exact Nat.le_of_mul_le_mul_left t1 (by omega)
  · -- upper
    have t1 : m' * ((T + 1) * (cA * c)) ≤ m' * ((T + 2) * x) := by
      calc m' * ((T + 1) * (cA * c)) = (T + 1) * (m' * (cA * c)) := by ring
        _ ≤ (T + 1) * ((j + 8) * x) := Nat.mul_le_mul_left _ hUp
        _ = (j + 8) * (T + 1) * x := by ring
        _ ≤ m' * (T + 2) * x := Nat.mul_le_mul_right _ hjT
        _ = m' * ((T + 2) * x) := by ring
    exact Nat.le_of_mul_le_mul_left t1 hm'pos

end Ruzsa785.Ladder

namespace Ruzsa785.Ladder

open Filter Finset
open scoped Pointwise Topology

variable {w : ℕ → ℝ} (D : Ladder w)

lemma mem_add_of_large {n : ℕ} (hn : D.Y 4 ≤ n) : n ∈ D.Aset + D.Bset := by
  obtain ⟨k, hk, hYk, hnk⟩ := stage D.Y D.Y_strictMono hn
  have hY := D.Y_eq k
  have hkX := D.le_X k
  obtain ⟨i, hi1, hik, hmod⟩ := D.cover_md hk n (by omega)
  have ha := D.av_strictMono.monotone hik
  refine Set.mem_add.2 ⟨D.av i, ⟨i - 1, ?_⟩,
    n - D.av i, ⟨k, hk, hmod.dvd', by omega, by omega⟩, by omega⟩
  show D.av (i - 1 + 1) = D.av i
  rw [Nat.sub_add_cancel hi1]

lemma A_infinite : D.Aset.Infinite := by
  apply Set.infinite_range_of_injective
  intro a b h
  have := D.av_strictMono.injective h
  omega

lemma B_infinite : D.Bset.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  let k := N + 4
  have hm : 0 < D.md k := D.md_pos (by dsimp [k]; omega)
  refine ⟨D.md k * (D.X k / D.md k + 1),
    ⟨k, by dsimp [k]; omega, dvd_mul_right _ _, (Nat.lt_mul_div_succ _ hm).le, ?_⟩, ?_⟩
  · have h1 : D.md k * (D.X k / D.md k + 1) =
        D.md k * (D.X k / D.md k) + D.md k := by ring
    have h2 := Nat.mul_div_le (D.X k) (D.md k)
    have h3 := D.md_le k
    have h4 := D.X_lt_succ k
    have h5 := D.Y_eq (k + 1)
    have h6 := D.le_av (k + 1)
    omega
  · have h1 := Nat.lt_mul_div_succ (D.X k) hm
    have h2 : N + 4 ≤ D.X k := D.le_X k
    omega

lemma A_zero : 0 ∉ D.Aset := by
  rintro ⟨i, hi⟩
  have h := D.av_pos (show 0 < i + 1 by omega)
  change D.av (i+1) = 0 at hi
  omega

lemma B_zero : 0 ∉ D.Bset := by
  rintro ⟨k, hk, -, hX, -⟩
  have := D.le_X k
  omega

lemma count_A_at_cutoff (k : ℕ) :
    Erdos785.counting D.Aset (D.av (k + 1) - 1) = k := by
  have heq : D.Aset ∩ Set.Icc 1 (D.av (k + 1) - 1) =
      (((Finset.Icc 1 k).image D.av : Finset ℕ) : Set ℕ) := by
    ext x
    constructor
    · rintro ⟨⟨i, rfl⟩, -, hx⟩
      change D.av (i + 1) ≤ D.av (k + 1) - 1 at hx
      have hp : 0 < D.av (k + 1) := D.av_pos (by omega)
      have hlt : D.av (i + 1) < D.av (k + 1) := by omega
      exact mem_coe.mpr (mem_image.mpr ⟨i+1, mem_Icc.mpr ⟨by omega,
        by have := D.av_strictMono.lt_iff_lt.mp hlt; omega⟩, rfl⟩)
    · intro hx
      obtain ⟨i, hi, rfl⟩ := mem_image.mp (mem_coe.mp hx)
      have hh := mem_Icc.mp hi
      have hp := D.av_pos (show 0 < i by omega)
      refine ⟨⟨i - 1, ?_⟩, hp, ?_⟩
      · show D.av (i - 1 + 1) = D.av i
        rw [Nat.sub_add_cancel hh.1]
      · have := D.av_strictMono (show i < k + 1 by omega)
        omega
  rw [Erdos785.counting, heq, Set.ncard_coe_finset,
    card_image_of_injective _ D.av_strictMono.injective, Nat.card_Icc]
  omega

lemma count_B_at_checkpoint {k : ℕ} (hk : D.Complete k) :
    Erdos785.counting D.Bset (D.av (k+1)-1) ≤ D.Y k + (D.av (k+1)-1) / k := by
  let x := D.av (k+1)-1
  let lo := Ioc 0 (D.Y k)
  let hi := (Ioc 0 x).filter (fun b => k ∣ b)
  have hx : x < D.X (k+1) := by
    have h := D.av_pos (show 0 < k + 1 by omega)
    have hle : D.av (k+1) ≤ D.X (k+1) := Nat.le_mul_of_pos_left _ (by omega)
    dsimp [x]
    omega
  have hsub : D.Bset ∩ Set.Icc 1 x ⊆ ((lo ∪ hi : Finset ℕ) : Set ℕ) := by
    rintro b ⟨⟨i, hi4, hdvd, hxib, hbY⟩, hb1, hbx⟩
    have hilt : i < k+1 := D.X_strictMono.lt_iff_lt.mp (by omega)
    rw [mem_coe, mem_union]
    rcases Nat.lt_or_eq_of_le (show i ≤ k by omega) with h | rfl
    · left
      have hle : D.Y (i+1) ≤ D.Y k := D.Y_strictMono.monotone (by omega)
      exact mem_Ioc.mpr ⟨by omega, by omega⟩
    · right
      rw [D.md_of_complete hk] at hdvd
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega,hbx⟩,hdvd⟩
  have hc := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset] at hc
  have hle := hc.trans (card_union_le lo hi)
  change (D.Bset ∩ Set.Icc 1 x).ncard ≤ (Ioc 0 (D.Y k)).card + ((Ioc 0 x).filter _).card at hle
  rwa [Nat.card_Ioc, Nat.sub_zero, Nat.Ioc_filter_dvd_card_eq_div] at hle

lemma excess_frequently_small : ∃ᶠ x : ℕ in atTop,
    (Erdos785.counting D.Aset x * Erdos785.counting D.Bset x : ℝ) - x < w x := by
  rw [frequently_atTop]
  intro N
  obtain ⟨k,hk,hc⟩ := D.complete (max N 4)
  let x := D.av (k+1) - 1
  have hx : N ≤ x := by have := D.le_av (k+1); dsimp [x]; omega
  have ha : Erdos785.counting D.Aset x = k := D.count_A_at_cutoff k
  have hb : Erdos785.counting D.Bset x ≤ D.Y k + x/k := D.count_B_at_checkpoint hc
  have hd : k * (x/k) ≤ x := Nat.mul_div_le _ _
  have hbound := Nat.mul_le_mul_left k hb
  have hsum : k * (D.Y k + x/k) = k * D.Y k + k * (x/k) := by ring
  have hmul : k * Erdos785.counting D.Bset x ≤ x + k * (k+1) * D.av k := by
    rw [hsum, Y] at hbound
    have he : k * ((k+1)*D.av k) = k * (k+1) * D.av k := by ring
    omega
  have hreal : (k : ℝ) * Erdos785.counting D.Bset x ≤
      (x : ℝ) + ((k*(k+1)*D.av k : ℕ) : ℝ) := by exact_mod_cast hmul
  refine ⟨x,hx,?_⟩
  rw [ha]
  linarith [(D.growth k).2.2]

lemma counts_tendsto : Tendsto
    (fun x : ℕ => (Erdos785.counting D.Aset x * Erdos785.counting D.Bset x : ℝ) / x)
    atTop (𝓝 1) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨T, hT⟩ := exists_nat_one_div_lt hε
  refine ⟨D.X ((9 * T + 10) ^ 2 + 5), fun x hx => ?_⟩
  obtain ⟨k, hk, hXk, hxk⟩ := stage D.X D.X_strictMono hx
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨hlo, hhi⟩ := D.ratio_bounds (j := j) (x := x) (T := T) (by omega) (by omega)
    hXk hxk
  unfold Erdos785.counting
  obtain ⟨N, hN⟩ : ∃ N : ℕ,
      N = (D.Aset ∩ Set.Icc 1 x).ncard * (D.Bset ∩ Set.Icc 1 x).ncard := ⟨_, rfl⟩
  rw [← hN] at hlo hhi
  have hxpos : (0 : ℝ) < x := by
    have h1 := D.le_X (j + 1)
    have h2 : 0 < x := by omega
    exact_mod_cast h2
  have hNr : ((D.Aset ∩ Set.Icc 1 x).ncard : ℝ) * ((D.Bset ∩ Set.Icc 1 x).ncard : ℝ)
      = (N : ℝ) := by
    rw [hN]; push_cast; ring
  rw [hNr, Real.dist_eq, div_sub_one hxpos.ne', abs_div, abs_of_pos hxpos, div_lt_iff₀ hxpos]
  have h1 : (T : ℝ) * x ≤ ((T : ℝ) + 1) * N := by exact_mod_cast hlo
  have h2 : ((T : ℝ) + 1) * N ≤ ((T : ℝ) + 2) * x := by exact_mod_cast hhi
  have hTpos : (0 : ℝ) < (T : ℝ) + 1 := by positivity
  have h3 : (1 : ℝ) < ε * ((T : ℝ) + 1) := by
    rw [div_lt_iff₀ hTpos] at hT
    exact hT
  have h4 : (x : ℝ) < ε * ((T : ℝ) + 1) * x := by nlinarith
  rw [abs_lt]
  constructor
  · have h5 : ((T : ℝ) + 1) * (-(ε * x)) < ((T : ℝ) + 1) * ((N : ℝ) - x) := by nlinarith
    exact lt_of_mul_lt_mul_left h5 hTpos.le
  · have h5 : ((T : ℝ) + 1) * ((N : ℝ) - x) < ((T : ℝ) + 1) * (ε * x) := by nlinarith
    exact lt_of_mul_lt_mul_left h5 hTpos.le

end Ruzsa785.Ladder

theorem OMA.solution : type_of% @Erdos785.erdos_785.variants.ruzsa_upper_bound := by
  intro w hw
  obtain ⟨D⟩ := Ruzsa785.make_ladder w hw
  refine ⟨D.Aset, D.Bset, D.A_infinite, D.B_infinite, D.A_zero, D.B_zero,
    ⟨Filter.eventually_atTop.2 ⟨D.Y 4, fun n hn => D.mem_add_of_large hn⟩, D.counts_tendsto⟩,
    D.excess_frequently_small⟩
