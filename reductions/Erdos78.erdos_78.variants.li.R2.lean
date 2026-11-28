import FormalConjectures.ErdosProblems.«78»

/-!
Li's sumset extractor (Theorem 1.7, arXiv 2303.06802) gives a symmetric
alternative to the ordered bipartite construction. The two sources here
are independent uniform draws from the same finite set. Each diagonal
pair has XOR zero, but the whole diagonal has only m of the m² draws.
-/
namespace OMA.R_Erdos78_erdos_78_variants_li_R2
open Erdos78 ComplexityTheory Filter Finset Real
open scoped Classical

/-- A colour occupying at least a quarter of the square must occur off the
diagonal once the set has more than four elements. -/
private theorem outsideDiagonal (S : Finset ℕ) (F : ℕ → Bool) (c : Bool)
    (hs : 4 < S.card)
    (many : S.card^2 ≤ 4*((S ×ˢ S).filter (fun z => F (z.1 ^^^ z.2) = c)).card) :
    ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ F (u ^^^ v) = c := by
  by_contra no
  have sub : ((S ×ˢ S).filter (fun z => F (z.1 ^^^ z.2) = c)) ⊆ S.diag := by
    intro z h
    obtain ⟨mem,col⟩ := mem_filter.mp h
    obtain ⟨hu,hv⟩ := mem_product.mp mem
    apply mem_diag.mpr
    exact ⟨hu,by by_contra ne; exact no ⟨z.1,hu,z.2,hv,ne,col⟩⟩
  have small := card_le_card sub
  rw [diag_card] at small
  have strict := Nat.mul_lt_mul_of_pos_right hs (by omega : 0 < S.card)
  rw [pow_two] at many
  omega

/-- Passing from binary width to a natural logarithm costs one exponent. -/
private theorem widthBound (D : ℕ) : ∀ᶠ n : ℕ in atTop,
    let m := ⌈(log (n : ℝ))^((D+1 : ℕ) : ℝ)⌉₊
    (Nat.log 2 n+1)^D ≤ m ∧ 4 < m := by
  let K : ℝ := 1 / log 2 + 1
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have eg : Tendsto (fun n : ℕ => log (n:ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eg.eventually_ge_atTop (max 5 (K^D))] with n hn
  let L := log (n:ℝ)
  have five : 5 ≤ L := (le_max_left ..).trans hn
  have kd : K^D ≤ L := (le_max_right ..).trans hn
  have lp : 0 ≤ L := by linarith
  have logBound : (Nat.log 2 n : ℝ) ≤ L * (1 / log 2) := by
    simpa [L,Real.logb,div_eq_mul_inv] using Real.natLog_le_logb n 2
  have width : (Nat.log 2 n : ℝ)+1 ≤ K*L := by dsimp [K]; linarith
  have est : ((Nat.log 2 n : ℝ)+1)^D ≤ L^(D+1) := calc
    _ ≤ (K*L)^D := pow_le_pow_left₀ (by positivity) width D
    _ = K^D * L^D := mul_pow .. 
    _ ≤ L * L^D := mul_le_mul_of_nonneg_right kd (pow_nonneg lp _)
    _ = L^(D+1) := by rw [pow_succ,mul_comm]
  have one : 1 ≤ L^D := one_le_pow₀ (by linarith) 
  have five' : 5 ≤ L^(D+1) := by
    rw [pow_succ]
    nlinarith only [five,mul_nonneg (sub_nonneg.mpr one) lp]
  rw [Real.rpow_natCast]
  constructor
  · apply (Nat.cast_le (α:=ℝ)).mp
    push_cast
    exact est.trans (Nat.le_ceil _)
  · have h : (5:ℝ) ≤ (⌈L^(D+1)⌉₊:ℝ) := five'.trans (Nat.le_ceil _)
    exact_mod_cast h

/-- A weak flat-source specialization of Li's one-input sumset extractor.
Uniform ordered pairs are sampled with replacement, so repeated sums have
their correct multiplicities. -/
def H1 : Prop := ∃ D : ℕ, ∃ f : List Bool × ℕ → Bool, IsPolyTime f ∧
    ∀ᶠ w : ℕ in atTop, ∀ S : Finset ℕ, (∀ a ∈ S, a < 2^w) → w^D ≤ S.card →
      ∀ c : Bool, S.card^2 ≤ 4*((S ×ˢ S).filter (fun z =>
        f (List.replicate w true,z.1 ^^^ z.2) = c)).card

/-- Polynomial-time preprocessing for the unary graph encoding: present the
bit width and the bitwise XOR of the two vertex labels to a one-input evaluator. -/
def H2 : Prop := ∀ f : List Bool × ℕ → Bool, IsPolyTime f →
    ∃ g : List Bool × ℕ × ℕ → Bool, IsPolyTime g ∧ ∀ s u v,
      g (s,u,v) = f (List.replicate (Nat.log 2 s.length + 1) true,u ^^^ v)

theorem main : H1 → H2 → type_of% @Erdos78.erdos_78.variants.li := by
  classical
  rintro ⟨D,f,hf,flat⟩ convert
  obtain ⟨g,hg,eval⟩ := convert f hf
  obtain ⟨w₀,hflat⟩ := eventually_atTop.mp flat
  refine ⟨((D+1:ℕ):ℝ),by positivity,g,hg,?_⟩
  filter_upwards [eventually_ge_atTop (2^w₀),widthBound D] with n hn hm
  let w := Nat.log 2 n+1
  let m := ⌈(log (n:ℝ))^((D+1:ℕ):ℝ)⌉₊
  let F (z : ℕ) := f (List.replicate w true,z)
  have start : w₀ ≤ w := (Nat.le_log_of_pow_le (by decide) hn).trans (Nat.le_succ _)
  have bound := Nat.lt_pow_succ_log_self (by decide : 1 < 2) n
  have cols (s : Finset (Fin n)) (sz : s.card=m) (c : Bool) :
      ∃ u ∈ s, ∃ v ∈ s, u ≠ v ∧ F (u.val ^^^ v.val)=c := by
    let e : Fin n ↪ ℕ := ⟨Fin.val,Fin.val_injective⟩
    let S := s.map e
    have sc : S.card = m := (card_map e).trans sz
    have lim (z) (h : z ∈ S) : z < 2^w := by
      obtain ⟨u,_,rfl⟩ := mem_map.mp h
      exact u.isLt.trans bound
    have prob := hflat w start S lim (sc ▸ hm.1) c
    obtain ⟨a,ha,b,hb,ne,col⟩ := outsideDiagonal S F c (sc ▸ hm.2) prob
    obtain ⟨i,hi,rfl⟩ := mem_map.mp ha
    obtain ⟨j,hj,rfl⟩ := mem_map.mp hb
    exact ⟨i,hi,j,hj,fun h => ne (congrArg e h),col⟩
  have edge (u v : Fin n) (ne : u ≠ v) :
      (explicitGraph g n).Adj u v ↔ F (u.val ^^^ v.val) = true := by
    simp [explicitGraph,eval,F,w,ne,Nat.xor_comm v.val u.val]
  constructor
  · intro s hs
    obtain ⟨u,hu,v,hv,ne,no⟩ := cols s hs.card_eq false
    have yes := (edge u v ne).mp (hs.isClique hu hv ne)
    simp [no] at yes
  · intro s hs
    obtain ⟨u,hu,v,hv,ne,yes⟩ := cols s hs.card_eq true
    exact ((SimpleGraph.compl_adj _ _ _).mp (hs.isClique hu hv ne)).2 ((edge u v ne).mpr yes)

end OMA.R_Erdos78_erdos_78_variants_li_R2
