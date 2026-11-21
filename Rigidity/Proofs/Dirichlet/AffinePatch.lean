import Rigidity.Proofs.Dirichlet.PatchingEstimates
import Rigidity.Proofs.Dirichlet.HardyCubeMoments

/-!
# Affine approximations on neighbouring cubes

The coordinates of the points of a cube of side `N` with corner `y` average to `y + (N − 1)/2`,
so the mesoscopic affine approximation is `ℓ_y(x) = ζ(y) + p(y)·(x − y − (N − 1)/2)` with
`ζ(y) = ⟨g⟩_{y+□}` and `p(y) = ⟨∇g⟩_{y+□}`. For neighbouring cubes `y` and `y' = y + N e_j` and an
edge `(x, x + e_j)` from the first to the second,
`ℓ_{y'}(x + e_j) − ℓ_y(x) = (ζ(y') − ζ(y) − N p_j(y)) +
  (p(y') − p(y))·(x + e_j − y' − (N−1)/2) + p_j(y)`,
which is the decomposition of the gradient of the patched affine functions across the faces of
the mesoscopic cubes in the proof of Armstrong–Dario, Lemma 6.3, Step 2.
-/

open Finset LatticeProb LatticeHC

namespace Rigidity.Dirichlet

open Rigidity.Percolation LatticeProb.Percolation

variable {d : ℕ}

/-- The slice of a cube at a value of one coordinate has exactly `N^{d−1}` points. -/
theorem card_filter_coord_eq (Q : IntegerCube d) (k : Fin d) {t : ℤ}
    (ht : t ∈ Finset.Ico (Q.corner k) (Q.corner k + Q.size)) :
    #(Q.vertices.filter fun x => x k = t) = Q.size ^ (d - 1) := by
  classical
  have heq : Q.vertices.filter (fun x => x k = t) = Fintype.piFinset (Function.update
      (fun j => Finset.Ico (Q.corner j) (Q.corner j + (Q.size : ℤ))) k {t}) := by
    ext x
    rw [Finset.mem_filter, IntegerCube.mem_vertices, Fintype.mem_piFinset]
    constructor
    · rintro ⟨hx, hxt⟩ j
      by_cases hj : j = k
      · subst hj
        simp [hxt]
      · rw [Function.update_of_ne hj]
        exact Finset.mem_Ico.mpr (hx j)
    · intro h
      have hk := h k
      simp only [Function.update_self, Finset.mem_singleton] at hk
      refine ⟨fun j => ?_, hk⟩
      by_cases hj : j = k
      · subst hj
        rw [hk]
        exact Finset.mem_Ico.mp ht
      · have := h j
        rw [Function.update_of_ne hj] at this
        exact Finset.mem_Ico.mp this
  rw [heq, card_piFinset_update, Finset.card_singleton, one_mul]

theorem sum_range_natCast (N : ℕ) :
    ∑ s ∈ Finset.range N, (s : ℝ) = (N : ℝ) * ((N : ℝ) - 1) / 2 := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- **Sum of a coordinate over a cube**: `Σ_{x ∈ y + □} (x_k − y_k) = N^{d−1} N (N − 1)/2`. -/
theorem sum_cornerCube_coord_sub (y : Vertex d) (N : ℕ) (k : Fin d) :
    ∑ x ∈ (cornerCube y N).vertices, ((x k - y k : ℤ) : ℝ) =
      (N : ℝ) ^ (d - 1) * ((N : ℝ) * ((N : ℝ) - 1) / 2) := by
  classical
  set Q := cornerCube y N
  set I := Finset.Ico (y k) (y k + (N : ℤ))
  have hmaps : ∀ x ∈ Q.vertices, x k ∈ I := fun x hx =>
    Finset.mem_Ico.mpr ((IntegerCube.mem_vertices Q x).mp hx k)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ t ∈ I, ∑ x ∈ Q.vertices.filter (fun x => x k = t), ((x k - y k : ℤ) : ℝ) =
      (N : ℝ) ^ (d - 1) * ((t - y k : ℤ) : ℝ) := by
    intro t ht
    rw [Finset.sum_congr rfl fun x hx => by rw [(Finset.mem_filter.mp hx).2], Finset.sum_const,
      nsmul_eq_mul, card_filter_coord_eq Q k ht]
    push_cast
    rfl
  rw [Finset.sum_congr rfl hfib, ← Finset.mul_sum]
  congr 1
  have h1 : ∑ t ∈ I, ((t - y k : ℤ) : ℝ) = ∑ t ∈ I, (((t - y k).toNat : ℕ) : ℝ) :=
    Finset.sum_congr rfl fun t ht => by
      simp only [I, Finset.mem_Ico] at ht
      have h0 : 0 ≤ t - y k := by linarith
      have := Int.toNat_of_nonneg h0
      exact_mod_cast this.symm
  rw [h1, sum_Ico_toNat_sub (y k) N (fun s => (s : ℝ)), sum_range_natCast]

/-- **The mesoscopic affine approximation in centred form**:
`ℓ_y(x) = ζ(y) + Σ_k p_k(y) ((x_k − y_k) − (N − 1)/2)`. -/
theorem cubeAffine_eq {N : ℕ} (hN : 0 < N) (g : Vertex d → ℝ) (y x : Vertex d) :
    cubeAffine N g y x = cubeAverage N g y +
      ∑ k, cubeSlope N g y k * (((x k - y k : ℤ) : ℝ) - ((N : ℝ) - 1) / 2) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  unfold cubeAffine
  set p := cubeSlope N g y
  have hav : cubeAverage N (fun z => g z - ∑ j, p j * ((z j - y j : ℤ) : ℝ)) y =
      cubeAverage N g y - ∑ j, p j * (((N : ℝ) - 1) / 2) := by
    unfold cubeAverage
    rw [Finset.sum_sub_distrib, Finset.sum_comm, sub_div]
    congr 1
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.mul_sum, sum_cornerCube_coord_sub]
    have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr fun h0 => (h0 ▸ j).elim0
    have hpow : (N : ℝ) ^ d = (N : ℝ) ^ (d - 1) * N := by
      rw [← pow_succ, Nat.sub_add_cancel hd]
    rw [hpow]
    field_simp
  rw [hav]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

/-- **Affine approximations across a face**: for neighbouring cubes `y` and `y' = y + N e_j`,
`ℓ_{y'}(x + e_j) − ℓ_y(x) = (ζ(y') − ζ(y) − N p_j(y)) +
  Σ_k (p_k(y') − p_k(y)) ((x + e_j − y')_k − (N − 1)/2) + p_j(y)`. -/
theorem cubeAffine_neighbour_sub {N : ℕ} (hN : 0 < N) (g : Vertex d → ℝ) (y x : Vertex d)
    (j : Fin d) :
    cubeAffine N g (y + (N : ℤ) • unit j) (x + unit j) - cubeAffine N g y x =
      (cubeAverage N g (y + (N : ℤ) • unit j) - cubeAverage N g y - N * cubeSlope N g y j) +
      ∑ k, (cubeSlope N g (y + (N : ℤ) • unit j) k - cubeSlope N g y k) *
        ((((x + unit j) k - (y + (N : ℤ) • unit j) k : ℤ) : ℝ) - ((N : ℝ) - 1) / 2) +
      cubeSlope N g y j := by
  classical
  rw [cubeAffine_eq hN, cubeAffine_eq hN]
  set p' := cubeSlope N g (y + (N : ℤ) • unit j)
  set p := cubeSlope N g y
  set c' : Fin d → ℝ := fun k =>
    (((x + unit j) k - (y + (N : ℤ) • unit j) k : ℤ) : ℝ) - ((N : ℝ) - 1) / 2
  set c : Fin d → ℝ := fun k => ((x k - y k : ℤ) : ℝ) - ((N : ℝ) - 1) / 2
  have hcc : ∀ k, c' k - c k = if k = j then 1 - (N : ℝ) else 0 := by
    intro k
    simp only [c', c, add_unit_apply]
    have hy : (y + (N : ℤ) • unit j) k = y k + if k = j then (N : ℤ) else 0 := by
      simp [unit, Pi.single_apply]
    rw [hy]
    split_ifs <;> push_cast <;> ring
  have hdiff : ∑ k, p k * (c' k - c k) = p j * (1 - N) := by
    simp only [hcc, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq' Finset.univ j, if_pos (Finset.mem_univ j)]
  have key : ∑ k, p' k * c' k - ∑ k, p k * c k =
      ∑ k, (p' k - p k) * c' k + ∑ k, p k * (c' k - c k) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have e1 : ∑ k, p' k * ((((x + unit j) k - (y + (N : ℤ) • unit j) k : ℤ) : ℝ) -
      ((N : ℝ) - 1) / 2) = ∑ k, p' k * c' k := rfl
  have e2 : ∑ k, p k * (((x k - y k : ℤ) : ℝ) - ((N : ℝ) - 1) / 2) = ∑ k, p k * c k := rfl
  rw [e1, e2]
  linarith [key, hdiff]

/-- **The jump across a face, bounded by slope oscillations**: for an edge `(x, x + e_j)` from the
cube `y + □` to the neighbouring cube `y' = y + N e_j`,
`(ℓ_{y'}(x + e_j) − ℓ_y(x))² ≤ 3 ((Σ_{t<N} |p_j(y + t e_j) − p_j(y)|)² +
  N² (Σ_k |p_k(y') − p_k(y)|)² + p_j(y)²)`. -/
theorem sq_cubeAffine_neighbour_sub_le {N : ℕ} (hN : 0 < N) (g : Vertex d → ℝ) (y x : Vertex d)
    (j : Fin d) (hx : x + unit j ∈ (cornerCube (y + (N : ℤ) • unit j) N).vertices) :
    (cubeAffine N g (y + (N : ℤ) • unit j) (x + unit j) - cubeAffine N g y x) ^ 2 ≤
      3 * ((∑ t ∈ Finset.range N,
          |cubeSlope N g (y + (t : ℤ) • unit j) j - cubeSlope N g y j|) ^ 2 +
        (N : ℝ) ^ 2 * (∑ k, |cubeSlope N g (y + (N : ℤ) • unit j) k - cubeSlope N g y k|) ^ 2 +
        cubeSlope N g y j ^ 2) := by
  rw [cubeAffine_neighbour_sub hN g y x j, cubeAverage_add_sub_sub_eq_sum]
  set a := ∑ t ∈ Finset.range N, (cubeSlope N g (y + (t : ℤ) • unit j) j - cubeSlope N g y j)
  set b := ∑ k, (cubeSlope N g (y + (N : ℤ) • unit j) k - cubeSlope N g y k) *
    ((((x + unit j) k - (y + (N : ℤ) • unit j) k : ℤ) : ℝ) - ((N : ℝ) - 1) / 2)
  set c := cubeSlope N g y j
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have ha : |a| ≤ ∑ t ∈ Finset.range N,
      |cubeSlope N g (y + (t : ℤ) • unit j) j - cubeSlope N g y j| :=
    Finset.abs_sum_le_sum_abs _ _
  have hb : |b| ≤ (N : ℝ) * ∑ k, |cubeSlope N g (y + (N : ℤ) • unit j) k - cubeSlope N g y k| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [abs_mul, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    rw [IntegerCube.mem_vertices] at hx
    have hk := hx k
    simp only [cornerCube] at hk
    rw [abs_le]
    have h1 : (0 : ℝ) ≤ (((x + unit j) k - (y + (N : ℤ) • unit j) k : ℤ) : ℝ) := by
      exact_mod_cast (by linarith [hk.1] : (0 : ℤ) ≤ (x + unit j) k - (y + (N : ℤ) • unit j) k)
    have h2 : (((x + unit j) k - (y + (N : ℤ) • unit j) k : ℤ) : ℝ) ≤ (N : ℝ) - 1 := by
      have : (x + unit j) k - (y + (N : ℤ) • unit j) k ≤ (N : ℤ) - 1 := by linarith [hk.2]
      exact_mod_cast this
    constructor <;> linarith
  have hA0 : 0 ≤ ∑ t ∈ Finset.range N,
      |cubeSlope N g (y + (t : ℤ) • unit j) j - cubeSlope N g y j| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hB0 : 0 ≤ (N : ℝ) * ∑ k, |cubeSlope N g (y + (N : ℤ) • unit j) k - cubeSlope N g y k| :=
    mul_nonneg hN'.le (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  have ha2 := pow_le_pow_left₀ (abs_nonneg a) ha 2
  have hb2 := pow_le_pow_left₀ (abs_nonneg b) hb 2
  rw [sq_abs] at ha2 hb2
  rw [mul_pow] at hb2
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]

end Rigidity.Dirichlet
