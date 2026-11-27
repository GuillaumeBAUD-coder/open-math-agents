import FormalConjectures.ErdosProblems.«61»
import Mathlib

/-! The subexponential Erdős–Hajnal bound. -/

open Finset Filter SimpleGraph
open scoped BigOperators Classical

namespace OMA61

noncomputable section

private def Fits {V : Type*} (G : SimpleGraph V) (b : Bool) (x y : V) : Prop :=
  if b then G.Adj x y else ¬ G.Adj x y

private lemma fits_symm {V : Type*} (G : SimpleGraph V) (b : Bool) (x y : V) :
    Fits G b x y ↔ Fits G b y x := by
  cases b <;> simp [Fits, adj_comm]

private def SparsePair {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (S : Finset V) (p m : ℕ) : Prop :=
  ∃ A ⊆ S, ∃ B ⊆ S, ∃ b : Bool, Disjoint A B ∧
    m ≤ A.card ∧ m ≤ B.card ∧
    ∀ x ∈ A, p*(B.filter (Fits G b x)).card ≤ B.card

private lemma group_partition {V : Type*} [DecidableEq V]
    (S : Finset V) (l m : ℕ) (h : l*m ≤ S.card) :
    ∃ A : Fin l → Finset V,
      (∀ i, A i ⊆ S ∧ (A i).card = m) ∧ Pairwise (fun i j => Disjoint (A i) (A j)) := by
  classical
  let e : Fin l × Fin m ↪ S := finProdFinEquiv.toEmbedding.trans
    ((Fin.castLEEmb h).trans (Fintype.equivFinOfCardEq (Fintype.card_coe S)).symm.toEmbedding)
  let E : Fin l × Fin m ↪ V := e.trans ⟨Subtype.val,Subtype.val_injective⟩
  let A (i : Fin l) := univ.map ⟨fun j => E (i,j), fun x y hxy => congrArg Prod.snd (E.injective hxy)⟩
  refine ⟨A,?_,?_⟩
  · intro i
    refine ⟨?_,by simp [A]⟩
    intro x hx
    obtain ⟨j,_,rfl⟩ := mem_map.1 hx
    exact (e (i,j)).property
  · intro i j hne
    rw [Finset.disjoint_left]
    intro x hx hy
    obtain ⟨u,_,hu⟩ := mem_map.1 hx
    obtain ⟨v,_,hv⟩ := mem_map.1 hy
    exact hne (congrArg Prod.fst (E.injective (hu.trans hv.symm)))

/-- Select one prescribed vertex at a time, retaining a fixed fraction in
each of the remaining groups. When no vertex can be selected, one of the
groups already forms a sparse or dense pair with many of the failed vertices. -/
private lemma pattern_or_pair {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (S : Finset V) (p m : ℕ) (hp : 0 < p) (hm : 0 < m) :
    ∀ {l : ℕ} (H : SimpleGraph (Fin l)) (A : Fin l → Finset V),
      (∀ i, A i ⊆ S ∧ (l+1)*m*p^l ≤ (A i).card) →
      Pairwise (fun i j => Disjoint (A i) (A j)) →
      (∃ f : Fin l ↪ V, (∀ i, f i ∈ A i) ∧ H = G.comap f) ∨
      SparsePair G S p m := by
  classical
  intro l
  induction l with
  | zero =>
    intro H A hA hd
    left
    refine ⟨⟨Fin.elim0,fun i => Fin.elim0 i⟩,fun i => Fin.elim0 i,?_⟩
    ext i
    exact Fin.elim0 i
  | succ l ih =>
    intro H A hA hd
    let b (j : Fin l) := decide (H.Adj 0 j.succ)
    let good (x : V) (j : Fin l) := (A j.succ).filter (Fits G (b j) x)
    have hgood : ∀ x j, good x j ⊆ A j.succ := fun _ _ => filter_subset _ _
    have hspec (x : V) (j : Fin l) (y : V) (hy : y ∈ good x j) :
        G.Adj x y ↔ H.Adj 0 j.succ := by
      have hy' : Fits G (b j) x y := (mem_filter.1 hy).2
      by_cases h : H.Adj 0 j.succ <;> simp_all [Fits,b]
    by_cases hex : ∃ x ∈ A 0, ∀ j, (A j.succ).card ≤ p*(good x j).card
    · obtain ⟨x,hx,hxg⟩ := hex
      have hcard (j : Fin l) : (l+1)*m*p^l ≤ (good x j).card := by
        apply Nat.le_of_mul_le_mul_left _ hp
        calc
          p*((l+1)*m*p^l) ≤ (l+1+1)*m*p^(l+1) := by
            rw [pow_succ]
            have hh : (l+1)*m ≤ (l+1+1)*m := Nat.mul_le_mul_right _ (by omega)
            simpa [mul_assoc,mul_comm,mul_left_comm] using Nat.mul_le_mul_right (p^l*p) hh
          _ ≤ (A j.succ).card := (hA _).2
          _ ≤ _ := hxg j
      obtain ⟨f,hf,hfg⟩ | hs := ih (H.comap Fin.succ) (good x)
        (fun i => ⟨(hgood x i).trans (hA _).1,hcard i⟩)
        (fun i j hij => (hd (fun h => hij (Fin.succ_inj.mp h))).mono (hgood x i) (hgood x j))
      · left
        let g : Fin (l+1) → V := Fin.cons x f
        have hg (i : Fin (l+1)) : g i ∈ A i := by
          induction i using Fin.cases with
          | zero => exact hx
          | succ i => exact hgood x i (hf i)
        have hginj : Function.Injective g := by
          intro i j hij
          by_contra! hne
          exact Finset.disjoint_left.1 (hd hne) (hg i) (hij ▸ hg j)
        refine ⟨⟨g,hginj⟩,hg,?_⟩
        ext i j
        change H.Adj i j ↔ G.Adj (g i) (g j)
        induction i using Fin.cases with
        | zero =>
          induction j using Fin.cases with
          | zero => simp [g]
          | succ j => exact (hspec x j (f j) (hf j)).symm
        | succ i =>
          induction j using Fin.cases with
          | zero => exact (H.adj_comm _ _).trans ((hspec x i (f i) (hf i)).symm.trans (G.adj_comm _ _))
          | succ j =>
            change (H.comap Fin.succ).Adj i j ↔ (G.comap f).Adj i j
            rw [hfg]
      · exact Or.inr hs
    · right
      let bad (j : Fin l) := (A 0).filter fun x => p*(good x j).card < (A j.succ).card
      have hcover : A 0 ⊆ univ.biUnion bad := by
        intro x hx
        simp only [not_exists, not_and, not_forall, not_le] at hex
        obtain ⟨j,hj⟩ := hex x hx
        exact mem_biUnion.2 ⟨j,mem_univ _,mem_filter.2 ⟨hx,hj⟩⟩
      have hpow : 1 ≤ p^(l+1) := Nat.one_le_pow _ _ hp
      have hsize (i : Fin (l+1)) : (l+1+1)*m ≤ (A i).card :=
        (Nat.le_mul_of_pos_right _ hpow).trans (hA i).2
      have he : ∃ j, m ≤ (bad j).card := by
        by_contra! h
        have hb := (card_le_card hcover).trans card_biUnion_le
        have hu : ∑ j, (bad j).card ≤ l*m := by
          simpa using sum_le_sum (s := (univ : Finset (Fin l))) (fun j _ => (h j).le)
        have hs := hsize 0
        nlinarith
      obtain ⟨j,hj⟩ := he
      exact ⟨bad j,(filter_subset _ _).trans (hA 0).1,A j.succ,(hA _).1,b j,
        (hd (Ne.symm (Fin.succ_ne_zero j))).mono_left (filter_subset _ _),hj,
        (Nat.le_mul_of_pos_left _ (by omega)).trans (hsize _),
        fun x hx => (mem_filter.1 hx).2.le⟩

private lemma sparse_pair_of_free {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    {l p m : ℕ} (H : SimpleGraph (Fin l)) (S : Finset V)
    (hfree : ¬∃ f : Fin l ↪ V, (∀ i, f i ∈ S) ∧ H = G.comap f)
    (hp : 0 < p) (hm : 0 < m) (hS : l*((l+1)*m*p^l) ≤ S.card) :
    SparsePair G S p m := by
  obtain ⟨A,hA,hd⟩ := group_partition S l _ hS
  obtain ⟨f,hf,heq⟩ | hpair := pattern_or_pair G S p m hp hm H A
    (fun i => ⟨(hA i).1,(hA i).2.ge⟩) hd
  · exact (hfree ⟨f,fun i => (hA i).1 (hf i),heq⟩).elim
  · exact hpair


private def Homog {V : Type*} (G : SimpleGraph V) (b : Bool) (A : Finset V) : Prop :=
  Set.Pairwise (A : Set V) (Fits G b)

private def OrderedWitness {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (S : Finset V) (d : ℕ) (b : Bool) : Prop :=
  ∃ A ⊆ S, ∃ B ⊆ S, Homog G b A ∧ Homog G (!b) B ∧ d ≤ A.card*B.card

private def Witness {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (S : Finset V) (d : ℕ) : Prop :=
  ∀ b, OrderedWitness G S d b

private lemma orient {V : Type*} [DecidableEq V] {G : SimpleGraph V} {S : Finset V} {b : Bool}
    {d : ℕ} (h : OrderedWitness G S d b) : Witness G S d := by
  intro c
  by_cases hcb : c = b
  · simpa [hcb] using h
  have hcb' : c = !b := by cases b <;> cases c <;> simp_all
  subst c
  obtain ⟨A,hA,B,hB,h₁,h₂,h₃⟩ := h
  exact ⟨B,hB,A,hA,h₂,by simpa using h₁,by simpa [mul_comm] using h₃⟩

private lemma homog_union {V : Type*} [DecidableEq V] {G : SimpleGraph V} {b : Bool}
    {A B : Finset V} (hA : Homog G b A) (hB : Homog G b B)
    (hcross : ∀ x ∈ A, ∀ y ∈ B, Fits G b x y) :
    Homog G b (A ∪ B) := by
  intro x hx y hy hxy
  rcases mem_union.1 hx with hx|hx <;> rcases mem_union.1 hy with hy|hy
  · exact hA hx hy hxy
  · exact hcross x hx y hy
  · exact (fits_symm G b y x).1 (hcross y hy x hx)
  · exact hB hx hy hxy

private lemma fits_not {V : Type*} (G : SimpleGraph V) (b : Bool) (x y : V) :
    ¬ Fits G b x y → Fits G (!b) x y := by
  classical
  cases b <;> simp [Fits]

private lemma reserve_half {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (A B : Finset V) (b : Bool) (p : ℕ) (hp : 0 < p)
    (hA : A.card ≤ p)
    (hbad : ∀ x ∈ A, (2*p)*(B.filter (Fits G b x)).card ≤ B.card) :
    ∃ B' ⊆ B, B.card ≤ 2*B'.card ∧ ∀ x ∈ A, ∀ y ∈ B', Fits G (!b) x y := by
  classical
  let bad := A.biUnion fun x => B.filter (Fits G b x)
  have hsubset : bad ⊆ B := by
    intro y hy
    obtain ⟨x,hx,hy⟩ := mem_biUnion.1 hy
    exact (mem_filter.1 hy).1
  let B' := B \ bad
  have hb : (2*p)*bad.card ≤ p*B.card := by
    calc
      _ ≤ (2*p)*(∑ x ∈ A, (B.filter (Fits G b x)).card) :=
        Nat.mul_le_mul_left _ card_biUnion_le
      _ = ∑ x ∈ A, (2*p)*(B.filter (Fits G b x)).card := mul_sum _ _ _
      _ ≤ ∑ _ ∈ A, B.card := sum_le_sum hbad
      _ = A.card*B.card := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ hA
  have hbb : 2*bad.card ≤ B.card := by
    apply Nat.le_of_mul_le_mul_left _ hp
    simpa [mul_left_comm,mul_assoc] using hb
  have hc : B'.card + bad.card = B.card := card_sdiff_add_card_eq_card hsubset
  refine ⟨B',sdiff_subset,by omega,?_⟩
  intro x hx y hy
  obtain ⟨hyB,hybad⟩ := mem_sdiff.1 hy
  exact fits_not G b x y fun h => hybad
    (mem_biUnion.2 ⟨x,hx,mem_filter.2 ⟨hyB,h⟩⟩)

private def threshold (l t : ℕ) := 2^(2*(l+2)*(t+1)^2)

private lemma threshold_step (l t : ℕ) :
    l*((l+1)*(2*threshold l t)*(2^(t+2))^l) ≤ threshold l (t+1) := by
  have hl : l ≤ 2^l := l.lt_two_pow_self.le
  have hs : l+1 ≤ 2^l := l.lt_two_pow_self
  calc
    _ ≤ 2^l*(2^l*(2*threshold l t)*(2^(t+2))^l) :=
      Nat.mul_le_mul hl (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hs))
    _ = 2^(l+l+1+2*(l+2)*(t+1)^2+(t+2)*l) := by
      rw [← pow_mul]
      simp only [threshold,pow_add,pow_one]
      ac_rfl
    _ ≤ _ := by
      apply Nat.pow_le_pow_right (by omega)
      nlinarith

private lemma witnesses {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    {l : ℕ} (H : SimpleGraph (Fin l)) :
    ∀ t (S : Finset V),
    (¬∃ f : Fin l ↪ V, (∀ i, f i ∈ S) ∧ H = G.comap f) →
    threshold l t ≤ S.card → Witness G S (2^t) := by
  classical
  intro t
  induction t with
  | zero =>
    intro S hfree hS b
    have hpos : 0 < S.card := (pow_pos (by decide) _).trans_le hS
    obtain ⟨x,hx⟩ := card_pos.1 hpos
    exact ⟨{x},singleton_subset_iff.2 hx,{x},singleton_subset_iff.2 hx,
      by simp [Homog],by simp [Homog],by simp⟩
  | succ t ih =>
    intro S hf hS
    have ht : 0 < threshold l t := pow_pos (by decide) _
    have inher (A : Finset V) (hA : A ⊆ S) :
        ¬∃ f : Fin l ↪ V, (∀ i, f i ∈ A) ∧ H = G.comap f := by
      rintro ⟨f,hf',heq⟩
      exact hf ⟨f,fun i => hA (hf' i),heq⟩
    obtain ⟨A,hA,B,hB,b,hAB,ha,hbb,hbad⟩ :=
      sparse_pair_of_free G H S hf (show 0 < 2^(t+2) by positivity)
        (show 0 < 2*threshold l t by positivity) ((threshold_step l t).trans hS)
    obtain ⟨X,hX,Y,hY,hx,hy,hXY⟩ := ih A (inher A hA) (by omega) (!b)
    by_cases hxB : 2^(t+1) ≤ X.card*Y.card
    · exact orient ⟨X,hX.trans hA,Y,hY.trans hA,hx,hy,hxB⟩
    have hYcard : 1 ≤ Y.card := by
      by_contra! hh
      have hy0 : Y.card = 0 := by omega
      rw [hy0,mul_zero] at hXY
      exact (not_lt_of_ge hXY) (by positivity)
    have hXcard : X.card ≤ 2^(t+1) :=
      (Nat.le_mul_of_pos_right _ hYcard).trans (le_of_not_ge hxB)
    obtain ⟨B',hB',hb',hcross⟩ :=
      reserve_half G X B b (2^(t+1)) (by positivity) hXcard (by
        intro x hm
        simpa [pow_succ,mul_comm] using hbad x (hX hm))
    have hsB := hB'.trans hB
    rw [pow_succ,mul_comm (2^t)]
    obtain ⟨Z,hZ,T,hT,hz,ht',hZT⟩ := ih B' (inher B' hsB) (by omega) (!b)
    have hXZ : Homog G (!b) (X ∪ Z) :=
      homog_union hx hz (fun x hx' y hy' => hcross x hx' y (hZ hy'))
    have hc : (X ∪ Z).card = X.card+Z.card :=
      card_union_of_disjoint (hAB.mono hX (hZ.trans hB'))
    have hs : X ∪ Z ⊆ S := union_subset (hX.trans hA) (hZ.trans hsB)
    obtain hle|hle := le_total Y.card T.card
    · apply orient (b := !b)
      refine ⟨X ∪ Z,hs,T,hT.trans hsB,hXZ,ht',?_⟩
      rw [hc,add_mul,two_mul]
      exact Nat.add_le_add (hXY.trans (Nat.mul_le_mul_left _ hle)) hZT
    · apply orient (b := !b)
      refine ⟨X ∪ Z,hs,Y,hY.trans hA,hXZ,hy,?_⟩
      rw [hc,add_mul,two_mul]
      exact Nat.add_le_add hXY (hZT.trans (Nat.mul_le_mul_left _ hle))



private lemma bracket_threshold {l n : ℕ} (hn : threshold l 1 ≤ n) :
    ∃ t, 1 ≤ t ∧ threshold l t ≤ n ∧ n < threshold l (t+1) := by
  let hE : ∃ i, n < threshold l (i+2) := by
    refine ⟨n,n.lt_two_pow_self.trans_le ?_⟩
    apply Nat.pow_le_pow_right (by omega)
    exact (show n ≤ (n+2+1)^2 by nlinarith).trans
      (Nat.le_mul_of_pos_left _ (by positivity))
  let i := Nat.find hE
  have hi : n < threshold l (i+2) := Nat.find_spec hE
  refine ⟨i+1,by omega,?_,hi⟩
  by_cases h : i = 0
  · simpa [h] using hn
  have ht := Nat.find_min hE (show i-1 < i by omega)
  rw [show i-1+2 = i+1 by omega] at ht
  exact le_of_not_gt ht

private def factor (l : ℕ) : ℝ := (2 : ℝ)*(l+2)*Real.log 2

private lemma factor_pos (l : ℕ) : 0 < factor l := by
  unfold factor
  positivity

private def rate (l : ℕ) : ℝ := Real.log 2 / (6*(Real.sqrt (factor l)+1))

private lemma rate_pos (l : ℕ) : 0 < rate l := by
  unfold rate
  positivity

private lemma exp_rate_sq {l n t : ℕ} (hn : 0 < n) (ht : 1 ≤ t)
    (hb : n < threshold l (t+1)) :
    Real.exp (rate l * Real.sqrt (Real.log (n:ℝ)))^2 ≤ (2:ℝ)^t := by
  let d := Real.sqrt (factor l)
  have hd : 0 ≤ d := Real.sqrt_nonneg _
  have hl : Real.log (n:ℝ) ≤ factor l*((t:ℝ)+2)^2 := by
    have hc : (n:ℝ) ≤ (threshold l (t+1):ℕ) := by exact_mod_cast hb.le
    have hh := Real.log_le_log (by exact_mod_cast hn) hc
    simp only [threshold,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow,Nat.cast_mul,Nat.cast_add,
      Nat.cast_one] at hh
    unfold factor
    linarith only [hh]
  have hs : Real.sqrt (Real.log (n:ℝ)) ≤ d*((t:ℝ)+2) := by
    refine (Real.sqrt_le_sqrt hl).trans_eq ?_
    rw [Real.sqrt_mul (factor_pos _).le, Real.sqrt_sq (by positivity)]
  have ht' : (1:ℝ) ≤ t := by exact_mod_cast ht
  have hs' : Real.sqrt (Real.log (n:ℝ)) ≤ 3*(t:ℝ)*(d+1) := by
    refine hs.trans ?_
    calc
      _ ≤ d*(3*(t:ℝ)) := mul_le_mul_of_nonneg_left (by linarith) hd
      _ ≤ _ := by
        rw [mul_comm d]
        apply mul_le_mul_of_nonneg_left (by linarith)
        positivity
  have hkey : rate l * Real.sqrt (Real.log (n:ℝ)) ≤ (t:ℝ)*Real.log 2/2 := by
    refine (mul_le_mul_of_nonneg_left hs' (rate_pos _).le).trans_eq ?_
    have hd' : d+1 ≠ 0 := by linarith
    change Real.log 2 / (6*(d+1)) * (3*(t:ℝ)*(d+1)) = _
    field_simp; norm_num
  rw [pow_two,← Real.exp_add,← Real.rpow_natCast,Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2)]
  exact Real.exp_le_exp.mpr (by linarith)

end

/-- Erdős and Hajnal's sparse-pair argument, using clique and independent-set
sizes together and a dyadic induction on the size of the desired witness.
See Erdős–Hajnal, [Ramsey-type theorems](https://doi.org/10.1016/0166-218X(89)90045-0). -/
theorem solution {α : Type*} [Fintype α] [DecidableEq α] (H : SimpleGraph α) :
    ∃ c > (0 : ℝ), Erdos61.IsErdosHajnalLowerBound H
      (fun n : ℕ => Real.exp (c * Real.sqrt (Real.log n))) := by
  classical
  let l := Fintype.card α
  let e := Fintype.equivFin α
  refine ⟨rate l,rate_pos l,?_⟩
  filter_upwards [eventually_ge_atTop (threshold l 1)] with n hn
  intro G hfree
  obtain ⟨t,ht,ht₁,ht₂⟩ := bracket_threshold hn
  have hn' : 0 < n := (pow_pos (by decide) _).trans_le hn
  have hf : ¬∃ f : Fin l ↪ Fin n, (∀ i, f i ∈ univ) ∧ H.comap e.symm = G.comap f := by
    rintro ⟨f,_,h⟩
    apply hfree
    refine ⟨e.toEmbedding.trans f,?_⟩
    ext x y
    have hh := congrArg (fun A : SimpleGraph (Fin l) => A.Adj (e x) (e y)) h
    simpa [SimpleGraph.comap_adj] using iff_of_eq hh
  obtain ⟨A,_,B,_,hA,hB,hprod⟩ :=
    witnesses G (H.comap e.symm) t univ hf (by simpa) true
  have hcl : G.IsClique A := by
    intro x hx y hy hxy
    simpa [Fits] using hA hx hy hxy
  have hind : G.IsIndepSet B := by
    intro x hx y hy hxy
    simpa [Fits] using hB hx hy hxy
  by_contra! hc
  have hAl : (A.card:ℝ) < Real.exp (rate l * Real.sqrt (Real.log (n:ℝ))) :=
    (Nat.cast_le.mpr hcl.card_le_cliqueNum).trans_lt hc.2
  have hBl : (B.card:ℝ) < Real.exp (rate l * Real.sqrt (Real.log (n:ℝ))) :=
    (Nat.cast_le.mpr hind.card_le_indepNum).trans_lt hc.1
  have hpr : (2:ℝ)^t ≤ (A.card:ℝ)*B.card := by exact_mod_cast hprod
  have he := exp_rate_sq hn' ht ht₂
  have hc' := mul_lt_mul'' hAl hBl (by positivity : (0:ℝ) ≤ A.card)
    (by positivity : (0:ℝ) ≤ B.card)
  rw [← pow_two] at hc'
  exact hc'.not_ge (he.trans hpr)

end OMA61

theorem OMA.solution : type_of% @Erdos61.erdos_61.variants.erha89 := by
  exact OMA61.solution