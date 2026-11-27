import OMAReductions.R_Erdos713_erdos_713_parts_i_R1

/-!
A finite forbidden graph with eventually linear extremal number must be a forest.
For prescribed degree and girth, act on the finite ball of words in involutive
generators. A short reduced word moves the empty word. The Cayley graph of the
resulting finite permutation group therefore has minimum degree as large as
required and no short cycle. A copy of a cyclic forbidden graph would give a
short cycle in this host.

The remaining forest cases are linear forests, star forests with branching,
and forests with both a branching vertex and an edge between nonleaves. Their
tasks use rational thresholds on edge counts. Crossing a higher threshold
arbitrarily late must force eventual attainment of each lower threshold.
This gives convergence, and disjoint edges give the limiting density at least
one half. For the path and star forest extremal formulas see Lidický, Liu and
Palmer, On the Turán number of forests, EJC 20 (2013), P62.
-/

-- Credit: @zarnab222-dev

section

open Finset

namespace E713Words

theorem ball (d q : ℕ) : ∃ W : Finset (List (Fin d)), ∀ l, l ∈ W ↔ l.length ≤ q := by
  classical
  induction q with
  | zero => exact ⟨{[]},fun l => by simp⟩
  | succ q ih =>
    obtain ⟨W,mem⟩ := ih
    let U := (univ : Finset (Fin d)).biUnion (fun i => W.image (List.cons i))
    refine ⟨insert [] U,?_⟩
    intro l
    cases l with
    | nil => simp
    | cons x xs => simp [U, mem]

theorem switches (d q : ℕ) : ∃ (W : Finset (List (Fin d))) (s : Fin d → Equiv.Perm W),
    (∀ l, l ∈ W ↔ l.length ≤ q) ∧
    (∀ i w, s i (s i w) = w) ∧
    (∀ i (u : W), u.val.length < q → u.val.head? ≠ some i → (s i u).val = i :: u.val) := by
  classical
  obtain ⟨W,mem⟩ := ball d q
  let toggle (i : Fin d) (l : List (Fin d)) := match l with
    | [] => if 0 < q then [i] else []
    | j::xs => if i=j then (if xs.head? = some i then j::xs else xs)
        else if xs.length+1 < q then i::j::xs else j::xs
  have push (i : Fin d) (l : List (Fin d)) (bound : l.length < q) (diff : l.head? ≠ some i) :
      toggle i l = i::l := by
    cases l with
    | nil => exact if_pos bound
    | cons j js =>
      have ne : i ≠ j := by rintro rfl; simp at diff
      simp only [List.length_cons] at bound
      simp [toggle,ne,bound]
  have pop (i : Fin d) (l : List (Fin d)) (diff : l.head? ≠ some i) :
      toggle i (i::l) = l := by simp [toggle,diff]
  have bound (i : Fin d) (l : List (Fin d)) (h : l.length ≤ q) : (toggle i l).length ≤ q := by
    cases l with
    | nil => by_cases small : 0 < q <;> (simp [toggle,small]; try omega)
    | cons j js =>
      simp only [List.length_cons] at h
      by_cases eq : i = j
      · subst j
        by_cases rep : js.head? = some i <;> simp only [toggle,if_pos rfl,rep,↓reduceIte,List.length_cons] <;> omega
      · by_cases room : js.length+1 < q <;> (simp [toggle,eq,room]; try omega)
  have twice (i : Fin d) (l : List (Fin d)) (h : l.length ≤ q) : toggle i (toggle i l) = l := by
    cases l with
    | nil =>
      by_cases pos : 0 < q
      · rw [push i [] pos (by simp), pop i [] (by simp)]
      · simp [toggle,pos]
    | cons j js =>
      by_cases eq : i=j
      · subst j
        by_cases repeatHead : js.head? = some i
        · simp [toggle,repeatHead]
        · rw [pop i js repeatHead, push i js (Nat.lt_of_succ_le h) repeatHead]
      · have diff : (j::js).head? ≠ some i := by simpa using Ne.symm eq
        by_cases space : (j::js).length < q
        · rw [push i _ space diff, pop i _ diff]
        · have noSpace : ¬ js.length+1 < q := space
          simp [toggle,eq,noSpace]
  let act (i : Fin d) (u : W) : W := ⟨toggle i u.val,(mem _).mpr (bound i _ ((mem _).mp u.property))⟩
  have invol (i : Fin d) (u : W) : act i (act i u) = u := Subtype.ext (twice i _ ((mem _).mp u.property))
  exact ⟨W,fun i => ⟨act i,act i,invol i,invol i⟩,mem,invol,fun i u => push i u.val⟩

theorem free_words (d q : ℕ) (hq : 2 ≤ q) :
    ∃ (W : Finset (List (Fin d))) (s : Fin d → Equiv.Perm W),
      Function.Injective s ∧ (∀ i, s i ≠ 1) ∧ (∀ i, s i * s i = 1) ∧
      ∀ l : List (Fin d), l ≠ [] → l.length ≤ q → l.IsChain (· ≠ ·) → (l.map s).prod ≠ 1 := by
  classical
  obtain ⟨W,s,mem,inv,push⟩ := switches d q
  let start : W := ⟨[],(mem []).mpr (by simp)⟩
  have travel (l : List (Fin d)) (hlen : l.length ≤ q) (reduced : l.IsChain (· ≠ ·)) :
      (((l.map s).prod start : W) : List (Fin d)) = l := by
    induction l with
    | nil => rfl
    | cons i xs ih =>
      have len : xs.length < q := Nat.lt_of_succ_le hlen
      have tail := reduced.tail
      have ihv := ih len.le tail
      have diff : xs.head? ≠ some i := by
        cases xs with
        | nil => simp
        | cons j js => simpa using (List.isChain_cons_cons.mp reduced).1.symm
      change (((s i) ((xs.map s).prod start) : W) : List (Fin d)) = i :: xs
      rw [push _ _ (by simpa only [ihv] using len) (by simpa only [ihv] using diff),ihv]
  have initial (i : Fin d) : ((s i start : W) : List (Fin d)) = [i] :=
    push i start (by change 0 < q; omega) (by simp [start])
  refine ⟨W,s,?_,?_,?_,?_⟩
  · intro i j eq
    have e := (initial i).symm.trans ((congrArg (fun p : Equiv.Perm W => (p start).val) eq).trans (initial j))
    simpa using e
  · intro i eq
    have t := initial i
    rw [eq] at t
    cases t
  · intro i
    ext u : 1
    exact inv i u
  · intro l ne len red eq
    have tr := travel l len red
    rw [eq] at tr
    exact ne tr.symm

end E713Words

end

section

open SimpleGraph Finset
namespace E713Cayley

theorem trail_word {P : Type*} [Group P] {d : ℕ} (gen : Fin d → P)
    (invol : ∀ i, gen i * gen i = 1) (X : SimpleGraph P)
    (adj : ∀ u v, X.Adj u v ↔ ∃ i, v = u * gen i) {u v : P} (p : X.Walk u v)
    (trail : p.IsTrail) :
    ∃ l : List (Fin d), l.length = p.length ∧ l.IsChain (· ≠ ·) ∧ v = u * (l.map gen).prod ∧
      ∀ i, l.head? = some i → s(u,u*gen i) ∈ p.edges := by
  induction p with
  | nil => exact ⟨[],rfl,by simp,by simp,by simp⟩
  | @cons a b c h tail ih =>
    obtain ⟨i,step⟩ := (adj a b).mp h
    obtain ⟨isTail,unused⟩ := (Walk.isTrail_cons h tail).mp trail
    obtain ⟨l,len,chain,prod,head⟩ := ih isTail
    have different : l.head? ≠ some i := by
      intro eq
      have used := head i eq
      have back : b * gen i = a := by rw [step,mul_assoc,invol,mul_one]
      rw [back,Sym2.eq_swap] at used
      exact unused used
    refine ⟨i::l,by simp [len],?_,?_,?_⟩
    · cases l with
      | nil => simp
      | cons j js =>
        exact List.isChain_cons_cons.mpr ⟨fun eq => different (by simp [eq]),chain⟩
    · simpa only [List.map_cons,List.prod_cons,← mul_assoc,← step] using prod
    · intro j eq
      have ij : i=j := Option.some.inj eq
      subst j
      rw [← step]
      simp

theorem host {P : Type*} [Group P] [Fintype P] {d q : ℕ} (gen : Fin d → P)
    (distinct : Function.Injective gen) (nontriv : ∀ i, gen i ≠ 1)
    (invol : ∀ i, gen i * gen i = 1)
    (short : ∀ l : List (Fin d), l ≠ [] → l.length ≤ q → l.IsChain (· ≠ ·) → (l.map gen).prod ≠ 1) :
    ∃ X : SimpleGraph P, (∀ u (I : Fintype (X.neighborSet u)), d ≤ @SimpleGraph.degree _ X u I) ∧
      ∀ u (p : X.Walk u u), p.IsCycle → q < p.length := by
  classical
  let X : SimpleGraph P := {
    Adj := fun u v => ∃ i, v=u*gen i
    symm := ⟨by
      rintro a b ⟨i,rfl⟩
      exact ⟨i,by rw [mul_assoc,invol,mul_one]⟩⟩
    loopless := ⟨by
      rintro a ⟨i,eq⟩
      exact nontriv i (mul_left_cancel (show a*gen i=a*1 by simpa using eq.symm))⟩ }
  have adj (u v : P) : X.Adj u v ↔ ∃ i, v=u*gen i := Iff.rfl
  refine ⟨X,?_,?_⟩
  · intro u I
    rw [Subsingleton.elim I (inferInstance : Fintype (X.neighborSet u))]
    let f (i : Fin d) : X.neighborSet u := ⟨u*gen i,⟨i,rfl⟩⟩
    have inject : Function.Injective f := fun i j eq => distinct (mul_left_cancel (congrArg Subtype.val eq))
    have count := Fintype.card_le_of_injective f inject
    simpa only [Fintype.card_fin,card_neighborSet_eq_degree] using count
  · intro u p cycle
    obtain ⟨l,len,chain,prod,_⟩ := trail_word gen invol X adj p cycle.isTrail
    by_contra! bound
    have ne : l ≠ [] := by
      rintro rfl
      have := cycle.three_le_length
      simp at len
      omega
    have one : (l.map gen).prod = 1 := mul_left_cancel (show u * (l.map gen).prod = u * 1 by simpa using prod.symm)
    exact short l ne (len ▸ bound) chain one

end E713Cayley

end

section

open SimpleGraph Finset Filter Asymptotics
open scoped Classical Topology
namespace E713Density

theorem even_lower {q : ℕ} (G : SimpleGraph (Fin q)) (branch : ∃ v, 2 ≤ G.degree v) (k : ℕ) :
    k ≤ extremalNumber (2*k) G := by
  classical
  let V := Fin k × Bool
  let X : SimpleGraph V := {
    Adj := fun a b => a.1=b.1 ∧ a.2≠b.2
    symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.symm⟩⟩
    loopless := ⟨fun _ h => h.2 rfl⟩ }
  have singleton (u : V) : X.neighborFinset u = {(u.1,!u.2)} := by
    ext v
    rcases u with ⟨i,b⟩
    rcases v with ⟨j,c⟩
    cases b <;> cases c <;> simp [V,X,mem_neighborFinset,Prod.mk.injEq,eq_comm]
  have deg (u : V) : X.degree u = 1 := by rw [← card_neighborFinset_eq_degree,singleton,card_singleton]
  have free : G.Free X := by
    rintro ⟨f⟩
    obtain ⟨v,hv⟩ := branch
    have lim := f.degree_le v
    rw [deg] at lim
    omega
  have sum := X.sum_degrees_eq_twice_card_edges
  simp only [deg,sum_const,card_univ,smul_eq_mul,mul_one] at sum
  have card : Fintype.card V = 2*k := by simp [V,Nat.mul_comm]
  have e := card_edgeFinset_le_extremalNumber free
  rw [card] at e sum
  omega

theorem positive_limit {q : ℕ} (G : SimpleGraph (Fin q)) (branch : ∃ v, 2 ≤ G.degree v) (c : ℝ)
    (lim : Tendsto (fun n : ℕ => (extremalNumber n G : ℝ) / n) atTop (𝓝 c)) :
    0 < c ∧ IsEquivalent atTop (fun n : ℕ => (extremalNumber n G : ℝ)) (fun n => c*n) := by
  have even : Tendsto (fun k : ℕ => 2*k) atTop atTop := tendsto_atTop.mpr (fun b =>
    eventually_atTop.mpr ⟨b,fun k hk => by omega⟩)
  have half : (1:ℝ)/2 ≤ c := by
    apply ge_of_tendsto (lim.comp even)
    filter_upwards [eventually_gt_atTop (0:ℕ)] with k hk
    change (1:ℝ)/2 ≤ (extremalNumber (2*k) G : ℝ)/(2*k:ℕ)
    have low : (k:ℝ) ≤ extremalNumber (2*k) G := by exact_mod_cast even_lower G branch k
    push_cast
    apply (le_div_iff₀ (by positivity)).mpr
    linarith
  have pos : 0 < c := by linarith
  refine ⟨pos,isEquivalent_of_tendsto_one ?_⟩
  have L := lim.div_const c
  rw [div_self pos.ne'] at L
  apply L.congr'
  filter_upwards with n
  change (extremalNumber n G : ℝ) / n / c = (extremalNumber n G : ℝ)/(c*n)
  rw [div_div,mul_comm]

theorem sustained {q : ℕ} (G : SimpleGraph (Fin q)) (C : ℕ)
    (cap : ∀ᶠ n : ℕ in atTop, extremalNumber n G ≤ C*n)
    (transfer : ∀ a b : ℚ, a < b →
      (∀ N, ∃ n ≥ N, b*n < (extremalNumber n G : ℚ)) →
      ∃ M, ∀ m ≥ M, a*m ≤ (extremalNumber m G : ℚ)) :
    ∃ c : ℝ, Tendsto (fun n : ℕ => (extremalNumber n G : ℝ)/n) atTop (𝓝 c) := by
  let u (n : ℕ) := (extremalNumber n G : ℝ)/n
  have above : atTop.IsBoundedUnder (· ≤ ·) u := by
    refine ⟨(C:ℝ),?_⟩
    change ∀ᶠ n : ℕ in atTop, u n ≤ (C:ℝ)
    filter_upwards [cap,eventually_gt_atTop (0:ℕ)] with n hn pos
    change (extremalNumber n G : ℝ)/n ≤ C
    exact (div_le_iff₀ (by positivity)).mpr (by exact_mod_cast hn)
  have below : atTop.IsBoundedUnder (· ≥ ·) u := by
    refine ⟨(0:ℝ),?_⟩
    change ∀ᶠ n : ℕ in atTop, 0 ≤ u n
    exact Eventually.of_forall (fun n => by dsimp [u]; positivity)
  apply tendsto_of_no_upcrossings (s := Set.range ((↑) : ℚ → ℝ)) Rat.denseRange_cast _ above below
  rintro _ ⟨a,rfl⟩ _ ⟨b,rfl⟩ ab ⟨down,up⟩
  have often : ∀ N, ∃ n ≥ N, b*n < (extremalNumber n G : ℚ) := by
    intro N
    obtain ⟨n,hn,high⟩ := frequently_atTop.mp up (N+1)
    have pos : 0 < n := by omega
    have high' := (lt_div_iff₀ (show (0:ℝ)<n by exact_mod_cast pos)).mp high
    exact ⟨n,by omega,by exact_mod_cast high'⟩
  obtain ⟨M,hM⟩ := transfer a b (by exact_mod_cast ab) often
  obtain ⟨n,hn,dip⟩ := frequently_atTop.mp down (M+1)
  have pos : 0 < n := by omega
  have dip' := (div_lt_iff₀ (show (0:ℝ)<n by exact_mod_cast pos)).mp dip
  have low := hM n (by omega)
  have low' : (a:ℝ)*n ≤ extremalNumber n G := by exact_mod_cast low
  exact (not_lt_of_ge low') dip'

end E713Density

end

section

open SimpleGraph Finset Filter
namespace E713Girth

/-- A forbidden graph containing a cycle cannot have eventually linear extremal number. -/
theorem acyclic_of_linear {q : ℕ} (G : SimpleGraph (Fin q)) (C : ℕ)
    (bound : ∀ᶠ n : ℕ in atTop, extremalNumber n G ≤ C*n) : G.IsAcyclic := by
  classical
  intro v walk cycle
  obtain ⟨N,large⟩ := eventually_atTop.mp bound
  let d := 2*C+N+2
  let k := G.edgeFinset.card+2
  obtain ⟨W,s,inject,ne,inv,words⟩ := E713Words.free_words d k (by dsimp [k]; omega)
  let P := Equiv.Perm W
  obtain ⟨X,deg,long⟩ := E713Cayley.host s inject ne inv words
  let n := Fintype.card P
  have pos : 0 < n := Fintype.card_pos
  have mindeg (u : P) : d ≤ X.degree u := deg u _
  have dlt : d < n := (mindeg 1).trans_lt (X.degree_lt_card_verts 1)
  have free : G.Free X := by
    rintro ⟨f⟩
    have mapped := (Walk.isCycle_map_iff_of_injective f.injective).mpr cycle
    have gt := long (f v) (walk.map f.toHom) mapped
    rw [Walk.length_map] at gt
    have le := cycle.isTrail.length_le_card_edgeFinset
    dsimp [k] at gt
    omega
  have maxE := card_edgeFinset_le_extremalNumber free
  have limit := large n (by dsimp [d] at dlt; omega)
  have edges : X.edgeFinset.card ≤ C*n := maxE.trans limit
  have lower := sum_le_sum (s := (univ : Finset P)) (fun u _ => mindeg u)
  rw [X.sum_degrees_eq_twice_card_edges, sum_const,card_univ,smul_eq_mul] at lower
  change n*d ≤ 2*X.edgeFinset.card at lower
  have stronger : n*(2*C) < n*d := Nat.mul_lt_mul_of_pos_left (by dsimp [d]; omega) pos
  nlinarith

end E713Girth


end

open SimpleGraph Finset Filter
open scoped Classical
namespace OMA.R_Erdos713_erdos_713_parts_i_R1_H2_R1

def H1 : Prop := ∀ (q : ℕ) (G : SimpleGraph (Fin q)), G.IsBipartite → G.IsAcyclic →
    2 ≤ G.edgeFinset.card → (∀ v, ¬ G.IsIsolated v) → ¬ G.Connected →
    (∃ v, 2 ≤ G.degree v) →
    (∀ v, G.degree v ≤ 2) →
    ∀ a b : ℚ, a < b →
    (∀ N, ∃ n ≥ N, b*n < (extremalNumber n G : ℚ)) →
    ∃ M, ∀ m ≥ M, a*m ≤ (extremalNumber m G : ℚ)

def H2 : Prop := ∀ (q : ℕ) (G : SimpleGraph (Fin q)), G.IsBipartite → G.IsAcyclic →
    2 ≤ G.edgeFinset.card → (∀ v, ¬ G.IsIsolated v) → ¬ G.Connected →
    (∃ v, 2 ≤ G.degree v) →
    (∃ v, 3 ≤ G.degree v) → (∀ v w, G.Adj v w → G.degree v ≤ 1 ∨ G.degree w ≤ 1) →
    ∀ a b : ℚ, a < b →
    (∀ N, ∃ n ≥ N, b*n < (extremalNumber n G : ℚ)) →
    ∃ M, ∀ m ≥ M, a*m ≤ (extremalNumber m G : ℚ)

def H3 : Prop := ∀ (q : ℕ) (G : SimpleGraph (Fin q)), G.IsBipartite → G.IsAcyclic →
    2 ≤ G.edgeFinset.card → (∀ v, ¬ G.IsIsolated v) → ¬ G.Connected →
    (∃ v, 2 ≤ G.degree v) →
    (∃ v, 3 ≤ G.degree v) → (∃ v w, G.Adj v w ∧ 2 ≤ G.degree v ∧ 2 ≤ G.degree w) →
    ∀ a b : ℚ, a < b →
    (∀ N, ∃ n ≥ N, b*n < (extremalNumber n G : ℚ)) →
    ∃ M, ∀ m ≥ M, a*m ≤ (extremalNumber m G : ℚ)

section
theorem main : H1 → H2 → H3 → OMA.R_Erdos713_erdos_713_parts_i_R1.H2 := by
  intro paths stars mixed q G bip edges active disc vertex linear
  classical
  obtain ⟨C,cap⟩ := linear
  have forest := E713Girth.acyclic_of_linear G C cap
  apply Exists.elim (E713Density.sustained G C cap ?_)
  · intro c lim
    exact ⟨c,E713Density.positive_limit G vertex c lim⟩
  · by_cases path : ∀ v, G.degree v ≤ 2
    · exact paths q G bip forest edges active disc vertex path
    have hub : ∃ v, 3 ≤ G.degree v := by
      push Not at path
      obtain ⟨v,hv⟩ := path
      exact ⟨v,by omega⟩
    by_cases star : ∀ v w, G.Adj v w → G.degree v ≤ 1 ∨ G.degree w ≤ 1
    · exact stars q G bip forest edges active disc vertex hub star
    push Not at star
    exact mixed q G bip forest edges active disc vertex hub star
end

end OMA.R_Erdos713_erdos_713_parts_i_R1_H2_R1
