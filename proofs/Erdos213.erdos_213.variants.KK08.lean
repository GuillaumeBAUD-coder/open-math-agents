import FormalConjectures.ErdosProblems.«213»

/-!
Seven lattice points from Kurz, Noll, Rathbun and Simmons, *Constructing 7-clusters*,
pp. 2–3. Integer arithmetic checks the distance, orientation and circle certificates.
-/

namespace OMA.Heptagon
open EuclideanGeometry

def x : Fin 7 → ℤ := ![0,327990000,238776720,222246024,243360000,198368352,176610000]
def y : Fin 7 → ℤ := ![0,0,118951040,-103907232,21896875,50379264,-94192000]
def dx (i j : Fin 7) := x i - x j
def dy (i j : Fin 7) := y i - y j
def height (i : Fin 7) := x i ^ 2 + y i ^ 2
def area (i j k : Fin 7) := dx i k * dy j k - dy i k * dx j k
def circleDet (i j k l : Fin 7) :=
  (height i - height l) * area j k l -
  (height j - height l) * area i k l + (height k - height l) * area i j l
def length : Fin 7 → Fin 7 → ℕ :=
  ![![0, 327990000, 266765200, 245336520, 244343125, 204665760, 200158000],
    ![327990000, 0, 148688800, 148251480, 87416875, 139067760, 178292000],
    ![266765200, 148688800, 0, 223470520, 97162325, 79592240, 222024000],
    ![245336520, 148251480, 223470520, 0, 127563605, 156123240, 46658680],
    ![244343125, 87416875, 97162325, 127563605, 0, 53249365, 133911125],
    ![204665760, 139067760, 79592240, 156123240, 53249365, 0, 146199440],
    ![200158000, 178292000, 222024000, 46658680, 133911125, 146199440, 0]]

lemma x_unique : ∀ i j, x i = x j → i = j := by decide
lemma distances : ∀ i j, (length i j : ℤ)^2 = (dx i j)^2 + (dy i j)^2 := by decide
lemma triangles : ∀ i j k, i ≠ j → j ≠ k → i ≠ k → area i j k ≠ 0 := by decide
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma circles : ∀ i j k l, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
    circleDet i j k l ≠ 0 := by decide

noncomputable def p (i : Fin 7) : ℝ² := !₂[(x i : ℝ), (y i : ℝ)]

lemma dist_sq (u v : ℝ²) : dist u v ^ 2 = (u 0-v 0)^2 + (u 1-v 1)^2 := by
  rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  rfl

lemma collinear_zero (u v w : ℝ²) (h : Collinear ℝ {u,v,w}) :
    (u 0-w 0)*(v 1-w 1)-(u 1-w 1)*(v 0-w 0)=0 := by
  obtain ⟨o,b,hh⟩ := (collinear_iff_exists_forall_eq_smul_vadd _).mp h
  obtain ⟨s,hs⟩ := hh u (by simp)
  obtain ⟨t,ht⟩ := hh v (by simp)
  obtain ⟨r,hr⟩ := hh w (by simp)
  rw [hs,ht,hr]
  change (s*b 0+o 0-(r*b 0+o 0))*(t*b 1+o 1-(r*b 1+o 1))-
    (s*b 1+o 1-(r*b 1+o 1))*(t*b 0+o 0-(r*b 0+o 0))=0
  ring

lemma height_diff (i l : Fin 7) (c : ℝ²) (h : dist (p i) c = dist (p l) c) :
    (height i : ℝ)-height l = 2*c 0*(dx i l)+2*c 1*(dy i l) := by
  have hh := congrArg (fun z : ℝ => z^2) h
  simp only [dist_sq] at hh
  change ((x i : ℝ)-c 0)^2+((y i : ℝ)-c 1)^2 =
    ((x l : ℝ)-c 0)^2+((y l : ℝ)-c 1)^2 at hh
  simp [height, dx, dy]
  linarith only [hh]

lemma on_circle_zero (i j k l : Fin 7) (c : ℝ²)
    (hi : dist (p i) c = dist (p l) c) (hj : dist (p j) c = dist (p l) c)
    (hk : dist (p k) c = dist (p l) c) : circleDet i j k l = 0 := by
  suffices h : (circleDet i j k l : ℝ) = 0 by exact_mod_cast h
  simp only [circleDet, Int.cast_add, Int.cast_sub, Int.cast_mul]
  rw [height_diff i l c hi, height_diff j l c hj, height_diff k l c hk]
  simp only [area, Int.cast_sub, Int.cast_mul]
  ring

end OMA.Heptagon

open OMA.Heptagon in
theorem OMA.solution : type_of% @Erdos213.erdos_213.variants.KK08 := by
  have inj : Function.Injective p := by
    intro i j h
    apply x_unique
    have hh := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 0) h
    change (x i : ℝ) = (x j : ℝ) at hh
    exact_mod_cast hh
  refine ⟨Set.range p, Set.finite_range _, ?_, ?_, ?_, ?_⟩
  · simp [Set.ncard_range_of_injective inj]
  · rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ _ ⟨k,rfl⟩ hij hjk hik h
    apply triangles i j k (hij ∘ congrArg p) (hjk ∘ congrArg p) (hik ∘ congrArg p)
    have hh := collinear_zero _ _ _ h
    change ((x i : ℝ)-x k)*(y j-y k : ℝ)-((y i : ℝ)-y k)*(x j-x k : ℝ)=0 at hh
    unfold area dx dy
    exact_mod_cast hh
  · rintro Q ⟨hQ,hcard⟩ ⟨c,r,h⟩
    obtain ⟨u,v,w,z,hu,hv,hw,hz,huv,huw,huz,hvw,hvz,hwz⟩ :=
      (Set.three_lt_ncard_iff ((Set.finite_range p).subset hQ)).mp (by omega)
    obtain ⟨i,rfl⟩ := hQ hu
    obtain ⟨j,rfl⟩ := hQ hv
    obtain ⟨k,rfl⟩ := hQ hw
    obtain ⟨l,rfl⟩ := hQ hz
    exact circles i j k l (huv ∘ congrArg p) (huw ∘ congrArg p) (huz ∘ congrArg p)
      (hvw ∘ congrArg p) (hvz ∘ congrArg p) (hwz ∘ congrArg p)
      (on_circle_zero i j k l c ((h _ hu).trans (h _ hz).symm)
        ((h _ hv).trans (h _ hz).symm) ((h _ hw).trans (h _ hz).symm))
  · rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ _
    refine ⟨(length i j : ℤ), ?_⟩
    have h := dist_sq (p i) (p j)
    change dist (p i) (p j)^2 = ((x i : ℝ)-x j)^2+((y i : ℝ)-y j)^2 at h
    have eq : (length i j : ℝ)^2 = ((x i : ℝ)-x j)^2+((y i : ℝ)-y j)^2 := by
      exact_mod_cast distances i j
    push_cast
    exact (sq_eq_sq₀ (by positivity) dist_nonneg).mp (eq.trans h.symm)
