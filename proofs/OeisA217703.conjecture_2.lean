import FormalConjectures.OEIS.«217703»
import Mathlib.Analysis.PSeries

/-! A proof by oscillation, avoiding evaluation of the huge integer witnesses
for A217703. For an eventually negative sequence the logarithmic difference
t and then its negative reciprocal would decrease by a divergent harmonic sum.
Credit: @Deldor14. -/
open OeisA217703 Finset
namespace OMA.Oscillation

private lemma harmonic_descent (g : ℕ → ℝ) (m : ℕ) (L : ℝ)
    (hl : ∀ k, L ≤ g k) (hd : ∀ k : ℕ, 1 / ((k+m : ℕ) : ℝ) ≤ g k - g (k+1)) : False := by
  apply Real.not_summable_one_div_natCast
  apply (summable_nat_add_iff (f := fun n : ℕ => 1/(n:ℝ)) m).mp
  apply summable_of_sum_range_le (c := g 0 - L) (fun _ => by positivity)
  intro N
  calc
    _ ≤ ∑ k ∈ range N, (g k - g (k+1)) := sum_le_sum (fun k _ => hd k)
    _ = g 0 - g N := sum_range_sub' g N
    _ ≤ _ := by linarith [hl N]

private lemma ratio_step {n t u : ℝ} (hn : 1 ≤ n) (hD : 0 < n + 2 + t) (ht : t ≤ n)
    (hu : u * (n * (n+2+t)) = (n+1)*(n*t-1)) :
    1/(n+1) ≤ 4*t - 4*u := by
  have hn' : 0 < n := by linarith
  have D : 0 < n*(n+2+t) := mul_pos hn' hD
  have hnum : n/2 ≤ n*(t^2+t+1)+1 := by
    nlinarith [mul_nonneg hn'.le (sq_nonneg (2*t+1))]
  have he : (t-u)*(n*(n+2+t)) = n*(t^2+t+1)+1 := by nlinarith only [hu]
  apply (div_le_iff₀ (by linarith : 0 < n+1)).2
  apply (le_of_mul_le_mul_right (a := n*(n+2+t)) ?_ D)
  nlinarith only [congrArg (fun z : ℝ => (n+1)*z) he, mul_nonneg (sub_nonneg.mpr hnum) (show 0 ≤ n+1 by linarith),
    mul_nonneg hn'.le (sub_nonneg.mpr ht)]

private lemma reciprocal_step {n t u : ℝ} (hn : 1 ≤ n) (ht : t ≤ -1) (hu' : u < 0)
    (hu : u * (n * (n+2+t)) = (n+1)*(n*t-1)) :
    1/(n+1) ≤ -4/t - (-4/u) := by
  have ht' : t < 0 := by linarith
  have E : 0 < (n+1)*(t*(n*t-1)) := by
    apply mul_pos (by linarith)
    apply mul_pos_of_neg_of_neg ht'
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ n) ht'.le]
  have he : (-4/t - (-4/u)) * ((n+1)*(t*(n*t-1))) = 4*(n*(t^2+t+1)+1) := by
    calc
      _ = -4*((n+1)*(n*t-1)) + (4/u)*t*((n+1)*(n*t-1)) := by
        field_simp [ht'.ne, hu'.ne] <;> ring
      _ = _ := by rw [← hu]; field_simp [hu'.ne]; nlinarith only [hu]
  apply (le_of_mul_le_mul_right (a := (n+1)*(t*(n*t-1))) ?_ E)
  rw [he]
  have hc : 1 / (n+1) * ((n+1)*(t*(n*t-1))) = t*(n*t-1) := by field_simp
  rw [hc]
  have quad : 0 ≤ 3*t^2 + 5*t + 4 := by nlinarith [sq_nonneg (6*t+5)]
  nlinarith [mul_nonneg (by linarith : 0 ≤ n) quad,
    mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hn) ht'.le]

private lemma impossible (t : ℕ → ℝ) (m : ℕ) (hm : 1 ≤ m)
    (hstep : ∀ k, let n : ℝ := (k+m:ℕ)
      0 < n+2+t k ∧ t k ≤ n ∧ t (k+1) * (n*(n+2+t k)) = (n+1)*(n*t k-1)) : False := by
  have hn (k : ℕ) : (1:ℝ) ≤ (k+m:ℕ) := by exact_mod_cast (show 1 ≤ k+m by omega)
  have hs (k : ℕ) := ratio_step (hn k) (hstep k).1 (hstep k).2.1 (hstep k).2.2
  have hanti : Antitone t := antitone_nat_of_succ_le fun k => by
    have := hs k
    have hpositive : (0:ℝ) < 1 / ((k+m:ℕ)+1:ℝ) := by positivity
    linarith
  obtain ⟨N,hN⟩ : ∃ N, t N ≤ -1 := by
    by_contra! h
    apply harmonic_descent (fun k => 4*t k) (m+1) (-4) (fun k => by linarith [h k])
    intro k
    simpa [add_assoc] using hs k
  have hlow (k : ℕ) : t (k+N) ≤ -1 := (hanti (show N ≤ k+N by omega)).trans hN
  apply harmonic_descent (fun k => -4 / t (k+N)) (N+m+1) 0
  · intro k; exact div_nonneg_of_nonpos (by norm_num) (by linarith [hlow k])
  · intro k
    have hu : t (k+N+1) < 0 := (hanti (Nat.le_succ _) |>.trans (hlow k)).trans_lt (by norm_num)
    have H := reciprocal_step (hn (k+N)) (hlow k) hu (hstep (k+N)).2.2
    convert H using 1 <;> push_cast <;> ring_nf

end OMA.Oscillation

namespace OMA.Oscillation
private lemma ratios {n A B C : ℝ} (hn : 0 < n) (ha : A < 0) (hb : B < 0) (hc : C < 0)
    (hrec : C = 2*n*(n+1)*B - n^4*A) :
    let t := n - n^3*A/B
    let u := (n+1) - (n+1)^3*B/C
    0 < n+2+t ∧ t ≤ n ∧ u*(n*(n+2+t)) = (n+1)*(n*t-1) := by
  dsimp only
  have he : n*(n+2+(n-n^3*A/B)) = C/B := by rw [hrec]; field_simp [hb.ne]; ring
  constructor
  · exact pos_of_mul_pos_right (he ▸ div_pos_of_neg_of_neg hc hb) hn.le
  constructor
  · have hr := div_nonneg_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hn.le 3) ha.le) hb.le
    linarith
  · rw [he]
    field_simp [hc.ne,hb.ne]
    rw [hrec]
    ring
private lemma no_negative_tail (m : ℕ) (h : ∀ k, a (k+m) < 0) : False := by
  let b (k : ℕ) : ℝ := a (k+m)
  let N (k : ℕ) : ℝ := (k+(m+1) : ℕ)
  let t (k : ℕ) := N k - (N k)^3*b k/b (k+1)
  have hb (k : ℕ) : b k < 0 := by
    dsimp only [b]
    exact_mod_cast h k
  have hN (k : ℕ) : 0 < N k := by dsimp [N]; positivity
  apply impossible t (m+1) (by omega)
  intro k
  have hrecz : a (k+m+2) =
      2*((k+m:ℕ)+1:ℤ)*(((k+m:ℕ)+1:ℤ)+1)*a (k+m+1) -
      ((k+m:ℕ)+1:ℤ)^4*a (k+m) := by rw [a]
  have hrec : b (k+2) = 2 * N k * (N k+1)*b (k+1) - (N k)^4*b k := by
    dsimp only [b,N]
    rw [show k+2+m=k+m+2 by omega, show k+1+m=k+m+1 by omega]
    rw [hrecz]
    push_cast
    ring
  have HH := ratios (hN k) (hb k) (hb (k+1)) (hb (k+2)) hrec
  have hsucc : N (k+1) = N k + 1 := by dsimp [N]; push_cast; ring
  change 0 < N k + 2 + t k ∧ t k ≤ N k ∧
    t (k+1) * (N k*(N k+2+t k)) = (N k+1)*(N k*t k-1)
  simpa only [t,hsucc] using HH
end OMA.Oscillation

theorem OMA.solution : type_of% @OeisA217703.conjecture_2 := by
  intro h
  exact OMA.Oscillation.no_negative_tail 2178 (fun k => (h _).2 (Or.inr (by omega)))
