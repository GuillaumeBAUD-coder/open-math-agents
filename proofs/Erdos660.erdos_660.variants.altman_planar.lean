import FormalConjectures.ErdosProblems.«660»

/-! # Distinct distances in convex polygons

Formalizes Altman's theorem that n points in strictly convex position in the plane determine at least floor(n/2) different distances. The supporting-line argument is from E. Altman, Some theorems on convex polygons, Canadian Mathematical Bulletin 15 (1972), with the referee's simplification. The cyclic order and diameter count are included below. -/

/- The cap-shortening argument of E. Altman, *Some theorems on convex
polygons* (1972), §III. The two intercepts on a chord are expressed by
oriented areas; this includes chords that share one end with the diameter. -/

open AffineMap
open scoped EuclideanGeometry

namespace OMA.Alt660

noncomputable section

def turn (a b c : ℝ²) : ℝ :=
  (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0)

theorem turn_cycle (a b c : ℝ²) : turn b c a = turn a b c := by unfold turn; ring
theorem turn_swap (a b c : ℝ²) : turn c b a = - turn a b c := by unfold turn; ring

private theorem line_turn (p q z : ℝ²) (a : ℝ) :
    turn p (lineMap p q a) z = a * turn p q z := by
  simp only [turn, lineMap_apply_module', PiLp.add_apply, PiLp.smul_apply,
    PiLp.sub_apply, smul_eq_mul]
  ring

private theorem intercept (σ : ℝ) (p q z A : ℝ²)
    (h : σ * turn p q A + σ * turn p z q ≠ 0) :
    lineMap z A (σ * turn p z q / (σ * turn p q A + σ * turn p z q)) =
      lineMap p q (σ * turn A p z / (σ * turn p q A + σ * turn p z q)) := by
  have hz (h : 0 < 2) : (⟨0,h⟩ : Fin 2) = 0 := rfl
  have ho (h : 1 < 2) : (⟨1,h⟩ : Fin 2) = 1 := rfl
  ext i
  fin_cases i <;>
    simp only [lineMap_apply_module', PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply,
      smul_eq_mul] <;>
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_add' _ _ _ h, div_add' _ _ _ h,
      div_left_inj' h] <;> simp only [turn, hz, ho] <;> ring

private theorem dilate_dist (z A B : ℝ²) (t : ℝ) :
    dist (lineMap z A t) (lineMap z B t) = |t| * dist A B := by
  rw [dist_eq_norm, lineMap_apply_module', lineMap_apply_module', add_sub_add_right_eq_sub,
    ← smul_sub, sub_sub_sub_cancel_right, norm_smul, Real.norm_eq_abs, ← dist_eq_norm]

private theorem intercept_dist (A B z : ℝ²) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 < t)
    (hst : s ≤ t) (hd : dist A z ≤ dist A B) :
    dist (lineMap z A s) z ≤ dist (lineMap z A s) (lineMap z B t) := by
  let P := lineMap z A (s / t)
  have hP : lineMap z P t = lineMap z A s := by
    rw [show P = _ from rfl, lineMap_lineMap_right]
    congr 1
    field_simp
  have hseg : 0 ≤ 1 - s/t := sub_nonneg.mpr ((div_le_one ht).2 hst)
  have he : dist A P + dist P z = dist A z := by
    rw [show P = _ from rfl, dist_right_lineMap, dist_lineMap_left,
      Real.norm_eq_abs, abs_of_nonneg hseg, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hs ht.le), dist_comm A z]
    ring
  have hcut : dist P z ≤ dist P B := by linarith [dist_triangle A P B]
  rw [← hP, dist_lineMap_left, dilate_dist, Real.norm_eq_abs, dist_comm z P]
  exact mul_le_mul_of_nonneg_left hcut (abs_nonneg t)

/-- When the diameter end A lies farther than B from the chord line,
the distance from p to each intervening vertex is strictly shorter than pq. -/
theorem shorten_left (σ : ℝ) (A p z q B : ℝ²)
    (hv : 0 ≤ σ * turn p q B) (hvu : σ * turn p q B ≤ σ * turn p q A)
    (hw : 0 < σ * turn p z q) (hap : 0 < σ * turn A p z)
    (hqb : 0 ≤ σ * turn z q B) (hab : 0 ≤ σ * turn A z B)
    (hd : dist A z ≤ dist A B) : dist p z < dist p q := by
  let u := σ * turn p q A
  let v := σ * turn p q B
  let w := σ * turn p z q
  have hu : 0 ≤ u := hv.trans hvu
  have hv' : 0 ≤ v := hv
  have hw' : 0 < w := hw
  have hu' : 0 < u + w := by positivity
  have hvw : 0 < v + w := by positivity
  let a := σ * turn A p z / (u+w)
  let b := σ * turn B p z / (v+w)
  let s := w / (u+w)
  let t := w / (v+w)
  have ha : 0 < a := div_pos hap hu'
  have hgap : σ * turn B p z * (u+w) - σ * turn A p z * (v+w) =
      w * (σ * turn A z B) := by dsimp [u,v,w,turn]; ring
  have hab' : a ≤ b := (div_le_div_iff₀ hu' hvw).2 (by nlinarith [mul_nonneg hw'.le hab])
  have hb : b ≤ 1 := by
    apply (div_le_one hvw).2
    have : v + w - σ * turn B p z = σ * turn z q B := by dsimp [v,w,turn]; ring
    linarith
  have hQ : lineMap z A s = lineMap p q a := intercept σ p q z A hu'.ne'
  have hR : lineMap z B t = lineMap p q b := intercept σ p q z B hvw.ne'
  have hst : s ≤ t := div_le_div_of_nonneg_left hw'.le hvw (by dsimp [u,v]; linarith)
  have hQR := intercept_dist A B z (div_nonneg hw'.le hu'.le) (div_pos hw' hvw) hst hd
  rw [hQ, hR] at hQR
  have htri : dist p z < dist p (lineMap p q a) + dist (lineMap p q a) z := by
    apply dist_lt_dist_add_dist_iff.2
    rintro ⟨r, _, hr⟩
    have he := congrArg (fun X => σ * turn p X z) hr
    simp only [line_turn] at he
    have h0 : turn p z z = 0 := by unfold turn; ring
    have hneg : turn p q z = -turn p z q := by unfold turn; ring
    rw [h0, hneg] at he
    nlinarith [mul_pos ha hw]
  rw [dist_left_lineMap, Real.norm_eq_abs, abs_of_pos ha] at htri
  rw [dist_lineMap_lineMap, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hab')] at hQR
  nlinarith [mul_nonneg (sub_nonneg.mpr hb) (dist_nonneg (x:=p) (y:=q))]

/-- In the oriented portion of a convex polygon running from one end of a
diameter to the other, one of the two ways of trimming a proper subchain
strictly shortens its chord. -/
theorem trim (v : ℕ → ℝ²) (k : ℕ)
    (orient : ∀ a b c : ℕ, a < b → b < c → c ≤ k → 0 < turn (v a) (v b) (v c))
    (diam : ∀ a b : ℕ, dist (v a) (v b) ≤ dist (v 0) (v k))
    (p q : ℕ) (hpq : p + 1 < q) (hqk : q < k) :
    dist (v p) (v (q-1)) < dist (v p) (v q) ∨
      dist (v (p+1)) (v q) < dist (v p) (v q) := by
  have pq : p < q := by omega
  have zp : 0 ≤ turn (v 0) (v p) (v q) := by
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · simp [turn]
    · exact (orient 0 p q hp pq hqk.le).le
  have pk : 0 < turn (v p) (v q) (v k) := orient p q k pq hqk le_rfl
  by_cases far : turn (v p) (v q) (v k) ≤ turn (v 0) (v p) (v q)
  · left
    have hp : 0 < p := by
      by_contra! h
      have : p = 0 := by omega
      simp [this, turn] at far pk
      linarith
    apply shorten_left 1 (v 0) (v p) (v (q-1)) (v q) (v k)
    · simpa using pk.le
    · simpa only [one_mul, turn_cycle (v 0) (v p) (v q)] using far
    · simpa using orient p (q-1) q (by omega) (by omega) hqk.le
    · simpa using orient 0 p (q-1) hp (by omega) (by omega)
    · simpa using (orient (q-1) q k (by omega) hqk le_rfl).le
    · simpa using (orient 0 (q-1) k (by omega) (by omega) le_rfl).le
    · exact diam 0 (q-1)
  · right
    have reversed (i j l : ℕ) :
        (-1:ℝ) * turn (v l) (v j) (v i) = turn (v i) (v j) (v l) := by
      rw [turn_swap]; ring
    rw [dist_comm (v (p+1)) (v q), dist_comm (v p) (v q)]
    apply shorten_left (-1) (v k) (v q) (v (p+1)) (v p) (v 0)
    · rwa [reversed]
    · rw [reversed, reversed, ← turn_cycle (v k) (v p) (v q)]
      exact (lt_of_not_ge far).le
    · rw [reversed]
      exact orient p (p+1) q (by omega) hpq hqk.le
    · rw [reversed]
      exact orient (p+1) q k hpq hqk le_rfl
    · rw [reversed]
      rcases Nat.eq_zero_or_pos p with rfl | hp
      · simp [turn]
      · exact (orient 0 p (p+1) hp (by omega) (by omega)).le
    · rw [reversed]
      exact (orient 0 (p+1) k (by omega) (by omega) le_rfl).le
    · rw [dist_comm (v k) (v 0)]
      exact diam k (p+1)

end

end OMA.Alt660

/- Altman's order argument: successively shorten a chord inside a cap cut off by a diameter.
When a maximal cap has half the polygon's sides, its penultimate chord cannot be a diameter:
reversing that chord would give a larger cap. -/

open scoped EuclideanGeometry
namespace OMA.AltCount660
open Finset

private lemma smaller {D : Finset ℝ} {x y : ℝ} (hx : x<y) (hy : y∈D) :
    (D.filter (·≤x)).card < (D.filter (·≤y)).card := by
  classical
  apply card_lt_card
  apply ssubset_iff_subset_ne.mpr
  refine ⟨fun a ha => mem_filter.mpr ⟨(mem_filter.mp ha).1, (mem_filter.mp ha).2.trans hx.le⟩, ?_⟩
  intro h
  have mem : y∈D.filter (·≤y) := mem_filter.mpr ⟨hy, le_rfl⟩
  rw [← h] at mem
  exact hx.not_ge (mem_filter.mp mem).2

private lemma chain {D : Finset ℝ} (v : ℕ → ℕ → ℝ) (k : ℕ)
    (mem : ∀ p q, p<q → q<k → v p q ∈ D)
    (short : ∀ p q, p+1<q → q<k → v p (q-1) < v p q ∨ v (p+1) q < v p q)
    (p q : ℕ) (hp : p<q) (hq : q<k) :
    q-p ≤ (D.filter (·≤v p q)).card := by
  classical
  have hmem := mem p q hp hq
  by_cases h1 : p+1=q
  · have pos : 0<(D.filter (·≤v p q)).card := card_pos.mpr ⟨v p q, by simp [hmem]⟩
    omega
  · rcases short p q (by omega) hq with left | right
    · have h := chain v k mem short p (q-1) (by omega) (by omega)
      have := smaller left hmem
      omega
    · have h := chain v k mem short (p+1) q (by omega) hq
      have := smaller right hmem
      omega
termination_by q-p

theorem count {X : Type*} [MetricSpace X] {n : ℕ} (hn : 2 ≤ n) (P : Finset X)
    (u : ℕ → X) (period : ∀ i, u (i+n)=u i) (member : ∀ i, u i ∈ P)
    (apart : ∀ i k, 0 < k → k < n → u i ≠ u (i+k))
    (diam : ℝ) (bound : ∀ i j, dist (u i) (u j) ≤ diam)
    (attained : ∃ i k : ℕ, 0<k ∧ k<n ∧ dist (u i) (u (i+k)) = diam)
    (short : ∀ i k : ℕ, 0<k → k<n → dist (u i) (u (i+k)) = diam →
        ∀ p q : ℕ, p+1<q → q<k →
        dist (u (i+p)) (u (i+(q-1))) < dist (u (i+p)) (u (i+q)) ∨
        dist (u (i+(p+1))) (u (i+q)) < dist (u (i+p)) (u (i+q))) :
    n/2 ≤ distinctDistances P := by
  classical
  let K := (Finset.range n).filter fun k => 0<k ∧ ∃ i, dist (u i) (u (i+k)) = diam
  have defK (k : ℕ) : k∈K ↔ k<n ∧ 0<k ∧ ∃ i, dist (u i) (u (i+k)) = diam := by simp [K]
  obtain ⟨a,b,hb,hn',hd⟩ := attained
  let k := K.max' ⟨b,(defK b).mpr ⟨hn',hb,a,hd⟩⟩
  obtain ⟨kn,kpos,i,di⟩ := (defK k).mp (max'_mem ..)
  have reverse (j d : ℕ) (hdp : 0<d) (hdn : d<n) (h : dist (u j) (u (j+d))=diam) :
      n-d ≤ k := by
    apply le_max'
    refine (defK _).mpr ⟨by omega,by omega,j+d,?_⟩
    rw [show j+d+(n-d) = j+n by omega,period,dist_comm,h]
  have back := reverse i k kpos kn di
  let D := distanceSet P
  have mem (j h : ℕ) (pos : 0<h) (small : h<n) : dist (u j) (u (j+h)) ∈ D := by
    apply mem_image.mpr
    exact ⟨(u j,u (j+h)),mem_offDiag.mpr ⟨member _,member _,apart j h pos small⟩, rfl⟩
  have dmem : diam ∈ D := di ▸ mem i k kpos kn
  change n/2 ≤ D.card
  by_cases low : k=1
  · have : 0<D.card := card_pos.mpr ⟨_,dmem⟩
    omega
  let v (p q : ℕ) := dist (u (i+p)) (u (i+q))
  have vm (p q : ℕ) (pq : p<q) (qk : q<k) : v p q ∈ D := by
    have := mem (i+p) (q-p) (by omega) (by omega)
    simpa only [show i+p+(q-p) = i+q by omega] using this
  have steps := chain v k vm (short i k kpos kn di) 0 (k-1) (by omega) (by omega)
  simp only [Nat.sub_zero] at steps
  have le : (D.filter (·≤v 0 (k-1))).card ≤ D.card := card_filter_le _ _
  by_cases half : n/2 ≤ k-1
  · omega
  have lt : v 0 (k-1) < diam := by
    refine lt_of_le_of_ne (bound _ _) ?_
    intro h
    have eq : dist (u i) (u (i+(k-1))) = diam := by simpa [v] using h
    have := reverse i (k-1) (by omega) (by omega) eq
    omega
  have inc := smaller lt dmem
  have full : (D.filter (·≤diam)).card ≤ D.card := card_filter_le _ _
  omega

end OMA.AltCount660

/- Unroll a cyclic enumeration of the polygon and choose a diameter for the chain argument. -/

open Finset
namespace OMA.AltCycle660

private lemma mod_offset {n : ℕ} (hn : 0<n) (i p : ℕ) (hp : p<n) :
    (i+p)%n = if i%n+p<n then i%n+p else i%n+p-n := by
  have hi := Nat.mod_lt i hn
  rw [Nat.add_mod, Nat.mod_eq_of_lt hp]
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

theorem separate {n : ℕ} (hn : 0<n) {i p q : ℕ} (hpq : p<q) (hq : q<n) :
    (i+p)%n ≠ (i+q)%n := by
  have hi := Nat.mod_lt i hn
  rw [mod_offset hn i p (by omega),mod_offset hn i q hq]
  split_ifs <;> omega

theorem ordered {X : Type*} (T : X → X → X → Prop)
    (rotate : ∀ a b c, T a b c → T b c a) {n : ℕ} (hn : 0<n) (e : Fin n → X)
    (pos : ∀ a b c, a<b → b<c → T (e a) (e b) (e c))
    (i p q r : ℕ) (pq : p<q) (qr : q<r) (rn : r<n) :
    T (e ⟨(i+p)%n,Nat.mod_lt _ hn⟩) (e ⟨(i+q)%n,Nat.mod_lt _ hn⟩)
      (e ⟨(i+r)%n,Nat.mod_lt _ hn⟩) := by
  let a : Fin n := ⟨(i+p)%n,Nat.mod_lt _ hn⟩
  let b : Fin n := ⟨(i+q)%n,Nat.mod_lt _ hn⟩
  let c : Fin n := ⟨(i+r)%n,Nat.mod_lt _ hn⟩
  change T (e a) (e b) (e c)
  have order : (a<b ∧ b<c) ∨ (b<c ∧ c<a) ∨ (c<a ∧ a<b) := by
    change (((i+p)%n < (i+q)%n) ∧ ((i+q)%n < (i+r)%n)) ∨
      (((i+q)%n < (i+r)%n) ∧ ((i+r)%n < (i+p)%n)) ∨
      (((i+r)%n < (i+p)%n) ∧ ((i+p)%n < (i+q)%n))
    have hi := Nat.mod_lt i hn
    rw [mod_offset hn i p (by omega),mod_offset hn i q (by omega),mod_offset hn i r rn]
    split_ifs <;> omega
  rcases order with ⟨h,k⟩ | ⟨h,k⟩ | ⟨h,k⟩
  · exact pos _ _ _ h k
  · exact rotate _ _ _ (rotate _ _ _ (pos _ _ _ h k))
  · exact rotate _ _ _ (pos _ _ _ h k)

theorem of_cycle {X : Type*} [MetricSpace X] {n : ℕ} (hn : 2≤n) (P : Finset X)
    (e : Fin n ≃ ↥P) (T : X → X → X → Prop) (rotate : ∀ a b c, T a b c → T b c a)
    (pos : ∀ a b c, a<b → b<c → T (e a) (e b) (e c))
    (shorten : ∀ (v : ℕ → X) (k : ℕ), 0 < k → k<n →
      (∀ a b c, a<b → b<c → c≤k → T (v a) (v b) (v c)) →
      (∀ p q, dist (v p) (v q) ≤ dist (v 0) (v k)) →
      ∀ p q : ℕ, p+1<q → q<k →
        dist (v p) (v (q-1)) < dist (v p) (v q) ∨
        dist (v (p+1)) (v q) < dist (v p) (v q)) :
    n/2 ≤ distinctDistances P := by
  classical
  have nz : 0<n := by omega
  let u (i : ℕ) : X := e ⟨i%n,Nat.mod_lt _ nz⟩
  have periodic (i : ℕ) : u (i+n) = u i := by simp [u]
  have inside (i : ℕ) : u i ∈ P := (e _).property
  have apart (i k : ℕ) (hk : 0<k) (kn : k<n) : u i ≠ u (i+k) := by
    intro eq
    have h := congrArg Fin.val (e.injective (Subtype.ext eq))
    exact separate nz (i:=i) (p:=0) hk kn (by simpa [u] using h)
  let D := distanceSet P
  have mem (x y : X) (hx : x∈P) (hy : y∈P) (ne : x≠y) : dist x y ∈ D :=
    mem_image.mpr ⟨(x,y), mem_offDiag.mpr ⟨hx,hy,ne⟩,rfl⟩
  have first := mem _ _ (inside 0) (inside (0+1)) (apart 0 1 (by decide) (by omega))
  let d := D.max' ⟨_, first⟩
  have dm : d∈D := max'_mem ..
  obtain ⟨⟨x,y⟩,hxy,xy⟩ := mem_image.mp dm
  obtain ⟨hx,hy,hne⟩ := mem_offDiag.mp hxy
  change dist x y = d at xy
  have maxd (i j : ℕ) : dist (u i) (u j) ≤ d := by
    by_cases eq : u i = u j
    · rw [eq,dist_self,←xy]; exact dist_nonneg
    · exact le_max' _ _ (mem _ _ (inside _) (inside _) eq)
  let a := e.symm ⟨x,hx⟩
  let b := e.symm ⟨y,hy⟩
  have pick (z : ↥P) : u (e.symm z).val = z := by simp [u, Nat.mod_eq_of_lt (e.symm z).isLt]
  have ax : u a.val = x := pick _
  have by' : u b.val = y := pick _
  have ne : a.val ≠ b.val := by intro h; exact hne (ax.symm.trans ((congrArg u h).trans by'))
  have reaches : ∃ i k : ℕ, 0<k ∧ k<n ∧ dist (u i) (u (i+k)) = d := by
    rcases lt_or_gt_of_ne ne with ab|ba
    · refine ⟨a.val,b.val-a.val,by omega,by have := b.isLt; omega,?_⟩
      rwa [show a.val+(b.val-a.val) = b.val by omega, ax, by']
    · refine ⟨b.val,a.val-b.val,by omega,by have := a.isLt; omega,?_⟩
      rwa [show b.val+(a.val-b.val)=a.val by omega, by', ax, dist_comm]
  apply OMA.AltCount660.count hn P u periodic inside apart d maxd reaches
  intro i k kpos kn top
  apply shorten (fun t => u (i+t)) k kpos kn
  · intro p q r pq qr rk
    exact ordered T rotate nz (fun j => (e j:X)) pos i p q r pq qr (by omega)
  · intro p q
    simpa only [Nat.add_zero,top] using maxd (i+p) (i+q)

end OMA.AltCycle660

/- Order convex-independent planar vertices by slope from a diameter endpoint.
A vertex between two rays cannot lie in the triangle they cut out with the
endpoint, forcing every triple in the resulting circular order to turn left. -/
namespace OMA.AltCap660
open Finset Set
open scoped Classical
private abbrev V := EuclideanSpace ℝ (Fin 2)

def turn (a b c : V) : ℝ :=
  (b 0-a 0)*(c 1-a 1)-(b 1-a 1)*(c 0-a 0)

private def dot (a d x : V) : ℝ := (d 0-a 0)*(x 0-a 0)+(d 1-a 1)*(x 1-a 1)
private def len (a b : V) : ℝ := (b 0-a 0)^2+(b 1-a 1)^2
private noncomputable def slope (a d x : V) := turn a d x / dot a d x

private theorem norm_pos {a b : V} (hne : a≠b) : 0<len a b := by
  by_contra! h
  apply hne
  dsimp [len] at h
  have e0 : b 0-a 0=0 := by nlinarith [sq_nonneg (b 1-a 1)]
  have e1 : b 1-a 1=0 := by nlinarith [sq_nonneg (b 0-a 0)]
  ext i
  rcases (show i=0 ∨ i=1 by omega) with rfl|rfl <;> linarith

private theorem no_triangle {P : Finset V} (hc : ConvexIndependent ℝ ((↑) : ↥(P:Set V) → V))
    {a b c x : V} (ha : a∈P) (hb : b∈P) (hd : c∈P) (hx : x∈P)
    (na : a≠x) (nb : b≠x) (nc : c≠x) {l r : ℝ} (hl : 0≤l) (hr : 0≤r) (hlr : l+r≤1)
    (eq : (1-l-r) • a + l • b + r • c = x) : False := by
  apply convexIndependent_set_iff_notMem_convexHull_sdiff.mp hc x hx
  apply mem_convexHull_of_exists_fintype (ι:=Fin 3) ![1-l-r,l,r] ![a,b,c]
  · intro i; fin_cases i <;> simp <;> linarith
  · simp [Fin.sum_univ_three]; ring
  · intro i; fin_cases i <;> simp [ha,hb,hd,na,nb,nc]
  · simpa [Fin.sum_univ_three,add_assoc] using eq

private theorem slope_strict {a d b c : V} (ad : a≠d) (pb : 0<dot a d b) (pc : 0<dot a d c)
    (h : slope a d b < slope a d c) : 0 < turn a b c := by
  have num := (div_lt_div_iff₀ pb pc).mp h
  have identity : len a d*turn a b c = dot a d b*turn a d c-turn a d b*dot a d c := by
    dsimp [dot,turn,len]; ring
  exact pos_of_mul_pos_right (by rw [identity]; linarith) (norm_pos ad).le

private theorem no_equal_ray {P : Finset V} (hc : ConvexIndependent ℝ ((↑) : ↥(P:Set V) → V))
    {a d x y : V} (ha : a∈P) (hx : x∈P) (hy : y∈P) (ax : a≠x) (yx : y≠x)
    (px : 0<dot a d x) (py : 0<dot a d y) (short : dot a d x ≤ dot a d y)
    (ray : turn a x y=0) : False := by
  let l := dot a d x / dot a d y
  apply no_triangle hc ha hy ha hx ax yx ax (l:=l) (r:=0) (by dsimp [l]; positivity) le_rfl
    (by dsimp [l]; simpa using (div_le_one py).mpr short)
  ext i
  simp only [sub_zero,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,zero_smul,add_zero]
  dsimp only [l]
  field_simp [py.ne']
  dsimp [turn] at ray
  dsimp [dot]
  rcases (show i=0 ∨ i=1 by omega) with rfl|rfl
  · linear_combination -(d 1-a 1)*ray
  · linear_combination (d 0-a 0)*ray

private theorem sorted_turn {P : Finset V} (hc : ConvexIndependent ℝ ((↑) : ↥(P:Set V) → V))
    {a b c d : V} (ha : a∈P) (hb : b∈P) (hc' : c∈P) (hd : d∈P)
    (ac : a≠c) (bc : b≠c) (dc : d≠c) (abc : 0<turn a b c)
    (abd : 0<turn a b d) (acd : 0<turn a c d) : 0<turn b c d := by
  by_contra! bad
  let l := turn a c d / turn a b d
  let r := turn a b c / turn a b d
  have lr : l+r≤1 := by
    dsimp [l,r]
    rw [←add_div,div_le_one abd]
    dsimp [turn] at bad ⊢
    linarith
  apply no_triangle hc ha hb hd hc' ac bc dc (by dsimp [l]; positivity) (by dsimp [r]; positivity) lr
  ext i
  simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
  dsimp only [l,r]
  field_simp [abd.ne']
  dsimp [turn]
  rcases (show i=0 ∨ i=1 by omega) with rfl|rfl <;> ring

private theorem slopes_injective {P : Finset V}
    (hc : ConvexIndependent ℝ ((↑) : ↥(P:Set V) → V)) {a d x y : V}
    (ha : a∈P) (ad : a≠d) (hx : x∈P) (hy : y∈P) (ax : a≠x) (ay : a≠y)
    (px : 0 < dot a d x) (py : 0 < dot a d y)
    (eq : slope a d x = slope a d y) : x=y := by
  by_contra neq
  have cross := (div_eq_div_iff px.ne' py.ne').mp eq
  have idn : len a d * turn a x y = dot a d x*turn a d y-turn a d x*dot a d y := by
    dsimp [len,turn,dot]; ring
  have ray : turn a x y = 0 := (mul_eq_zero.mp (show len a d * turn a x y = 0 by
    rw [idn]; linarith)).resolve_left (norm_pos ad).ne'
  rcases le_total (dot a d x) (dot a d y) with h|h
  · exact no_equal_ray hc ha hx hy ax (Ne.symm neq) px py h ray
  · exact no_equal_ray hc ha hy hx ay neq py px h (by dsimp [turn] at ray ⊢; linarith)

/-- Enumerate the vertices in positive circular order without assuming a polygon structure. -/
theorem ordering (P : Finset V) (hn : 2 ≤ P.card)
    (hc : ConvexIndependent ℝ ((↑) : ↥(P:Set V) → V)) :
    ∃ e : Fin P.card ≃ ↥P, ∀ i j k, i<j → j<k → 0 < turn (e i) (e j) (e k) := by
  classical
  obtain ⟨u,hu,v,hv,uv⟩ := Finset.one_lt_card.mp hn
  have non : P.Nonempty := ⟨u,hu⟩
  obtain ⟨⟨a,d⟩,mem,diam⟩ := (P ×ˢ P).exists_max_image (fun w => len w.1 w.2) (non.product non)
  obtain ⟨ha,hd⟩ := Finset.mem_product.mp mem
  have ad : a ≠ d := by
    intro e
    have H := diam (u,v) (Finset.mem_product.mpr ⟨hu,hv⟩)
    simp [e,len] at H
    exact (not_le.mpr (norm_pos uv)) H
  have dp (x : V) (hx : x∈P) (ax : x≠a) : 0<dot a d x := by
    have H := diam (d,x) (Finset.mem_product.mpr ⟨hd,hx⟩)
    have hp := norm_pos ax.symm
    dsimp [len] at H hp
    dsimp [dot]
    nlinarith
  obtain ⟨x₀,_,hmin⟩ := P.exists_min_image (slope a d) non
  let key (x : V) : ℝ := if x=a then slope a d x₀-1 else slope a d x
  have other (x : V) (hx : x∈P) (nx : x≠a) : key a < key x := by
    simp only [key,if_pos rfl,if_neg nx]
    linarith [hmin x hx]
  have amin (x : V) (hx : x∈P) : key a ≤ key x := by
    by_cases h:x=a
    · simp [h]
    · exact (other x hx h).le
  have inj : Set.InjOn key P := by
    intro x hx y hy eq
    by_cases nx:x=a
    · subst x
      by_contra ny
      exact (other y hy (Ne.symm ny)).ne eq
    by_cases ny:y=a
    · subst y
      exact False.elim ((other x hx nx).ne' eq)
    exact slopes_injective hc ha ad hx hy (Ne.symm nx) (Ne.symm ny) (dp x hx nx) (dp y hy ny)
      (by simpa [key,nx,ny] using eq)
  let keys := P.image key
  let g (x : ↥P) : ↥keys := ⟨key x, Finset.mem_image_of_mem _ x.property⟩
  have bij : Function.Bijective g := by
    constructor
    · intro x y eq
      exact Subtype.ext (inj x.property y.property (congrArg Subtype.val eq))
    · intro y
      obtain ⟨x,hx,eq⟩ := Finset.mem_image.mp y.property
      exact ⟨⟨x,hx⟩,Subtype.ext eq⟩
  let equiv := Equiv.ofBijective g bij
  let o := keys.orderIsoOfFin (Finset.card_image_of_injOn inj)
  let e : Fin P.card ≃ ↥P := o.toEquiv.trans equiv.symm
  have kval (i : Fin P.card) : key (e i) = (o i).val :=
    congrArg Subtype.val (equiv.apply_symm_apply (o i))
  have inc {i j : Fin P.card} (lt : i<j) : key (e i)<key (e j) := by
    rw [kval,kval]; exact o.strictMono lt
  refine ⟨e,fun i j k ij jk => ?_⟩
  have xy := inc ij
  have yz := inc jk
  have ny : (e j).val ≠ a := fun eq => by
    rw [eq] at xy; exact xy.not_ge (amin _ (e i).property)
  have nz : (e k).val ≠ a := fun eq => by
    rw [eq] at yz; exact yz.not_ge (amin _ (e j).property)
  have syz : slope a d (e j)<slope a d (e k) := by simpa [key,ny,nz] using yz
  have tri := slope_strict ad (dp _ (e j).property ny) (dp _ (e k).property nz) syz
  by_cases nx : (e i).val = a
  · simpa [nx] using tri
  have sxy : slope a d (e i)<slope a d (e j) := by simpa [key,nx,ny] using xy
  apply sorted_turn hc ha (e i).property (e j).property (e k).property ny.symm
    (fun eq => xy.ne (congrArg key eq)) (fun eq => yz.ne' (congrArg key eq))
  · exact slope_strict ad (dp _ (e i).property nx) (dp _ (e j).property ny) sxy
  · exact slope_strict ad (dp _ (e i).property nx) (dp _ (e k).property nz) (sxy.trans syz)
  · exact tri

end OMA.AltCap660

/- Apply Altman's shortening argument to a cyclic enumeration of the vertices. -/

open scoped EuclideanGeometry

namespace OMA.Alt660

theorem of_enum (enumerate : ∀ P : Finset ℝ², 2≤P.card →
    ConvexIndependent ℝ ((↑) : ↥(P:Set ℝ²) → ℝ²) → affineSpan ℝ (P:Set ℝ²)=⊤ →
    ∃ e : Fin P.card ≃ ↥P, ∀ i j k, i<j → j<k → 0<turn (e i) (e j) (e k)) :
    type_of% @Erdos660.erdos_660.variants.altman_planar := by
  intro n P card extreme span
  subst n
  by_cases large : 2≤P.card
  · obtain ⟨e,order⟩ := enumerate P large extreme span
    exact OMA.AltCycle660.of_cycle large P e (fun a b c => 0<turn a b c)
      (fun a b c h => (turn_cycle a b c).symm ▸ h) order
      (fun v k _ _ orient diam => trim v k orient diam)
  · omega

end OMA.Alt660

theorem OMA.solution : type_of% @Erdos660.erdos_660.variants.altman_planar :=
  OMA.Alt660.of_enum (fun P hn hc _ => OMA.AltCap660.ordering P hn hc)
