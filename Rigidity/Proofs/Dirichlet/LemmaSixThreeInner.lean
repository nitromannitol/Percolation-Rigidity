import Rigidity.Proofs.Dirichlet.LemmaSixThreeNormalized
import Rigidity.Proofs.Dirichlet.LemmaSixTwoInner

/-!
# Lemma 6.3 on the lattice with the edges inside the cube

Applying `edgeEnergy_patch_dirichletSolution_div_le` to the projected datum `w ∘ cubeProj Q`, whose
homogenized solution agrees with that of `w` on `Q`, gives the energy estimate (ii) of Lemma 6.3
for the energies of the edges inside `Q` (`innerEdgeEnergy_patch_dirichletSolution_div_le`), with
the mesoscopic hypotheses stated for the homogenized solution of `w` and all sums of `w` over the
edges inside `Q`. Together with `innerEdgeEnergy_dirichletSolution_div_le_of_mu_test` (Lemma 6.2)
both comparisons are for the same energy, as needed in the chain of Proposition 6.1.
-/

open Finset LatticeProb LatticeHC

namespace Rigidity.Dirichlet

open Rigidity.Percolation LatticeProb.Percolation

variable {d : ℕ}

/-- The mesoscopic slope only depends on the function on the cube and its steps. -/
theorem cubeSlope_congr {N : ℕ} {g g' : Vertex d → ℝ} {y : Vertex d}
    (h0 : ∀ x ∈ (cornerCube y N).vertices, g x = g' x)
    (h1 : ∀ x ∈ (cornerCube y N).vertices, ∀ k : Fin d, g (x + unit k) = g' (x + unit k))
    (k : Fin d) : cubeSlope N g y k = cubeSlope N g' y k := by
  simp only [cubeSlope, cubeAverage]
  congr 1
  exact Finset.sum_congr rfl fun x hx => by rw [h0 x hx, h1 x hx k]

/-- The affine approximation only depends on the function on the cube and its steps. -/
theorem cubeAffine_congr {N : ℕ} {g g' : Vertex d → ℝ} {y : Vertex d}
    (h0 : ∀ x ∈ (cornerCube y N).vertices, g x = g' x)
    (h1 : ∀ x ∈ (cornerCube y N).vertices, ∀ k : Fin d, g (x + unit k) = g' (x + unit k))
    (x : Vertex d) : cubeAffine N g y x = cubeAffine N g' y x := by
  simp only [cubeAffine, cubeAverage, cubeSlope_congr h0 h1]
  congr 2
  exact Finset.sum_congr rfl fun z hz => by rw [h0 z hz]

/-- Points at depth at least one in `Q` stay in `Q` after a step `e_k`. -/
theorem add_unit_mem_of_mem_shrinkCube (Q : IntegerCube d) {t : ℕ} (ht : 1 ≤ t) {x : Vertex d}
    (hx : x ∈ (shrinkCube Q t).vertices) (k : Fin d) :
    x ∈ Q.vertices ∧ x + unit k ∈ Q.vertices := by
  rw [mem_shrinkCube_iff] at hx
  constructor
  · rw [IntegerCube.mem_vertices]
    intro i
    have h := hx i
    have : ((Q.size - 2 * t : ℕ) : ℤ) ≤ (Q.size : ℤ) - 2 * t ∨ Q.size < 2 * t := by omega
    constructor <;> omega
  · rw [IntegerCube.mem_vertices]
    intro i
    rw [add_unit_apply]
    have h := hx i
    have : ((Q.size - 2 * t : ℕ) : ℤ) ≤ (Q.size : ℤ) - 2 * t ∨ Q.size < 2 * t := by omega
    split_ifs <;> constructor <;> omega

/-- The homogenized solutions of `w` and `w ∘ cubeProj Q` agree on `Q`. -/
theorem dirichletSolution_comp_cubeProj_of_mem (a : Fin d → ℝ) (Q : IntegerCube d)
    (w : Vertex d → ℝ) {x : Vertex d} (hx : x ∈ Q.vertices) :
    dirichletSolution (constCond a) (cubeInterior Q) (fun y => w (cubeProj Q y)) x =
      dirichletSolution (constCond a) (cubeInterior Q) w x :=
  dirichletSolution_comp_cubeProj _ Q w hx

/-- The squared gradient sums of the homogenized solution of the projected datum are the sums
over the edges inside `Q`. -/
theorem sum_sq_grad_dirichletSolution_comp_cubeProj (a : Fin d → ℝ) (Q : IntegerCube d)
    (w : Vertex d → ℝ) :
    ∑ x ∈ Q.vertices, ∑ k : Fin d,
        (dirichletSolution (constCond a) (cubeInterior Q) (fun y => w (cubeProj Q y)) (x + unit k) -
          dirichletSolution (constCond a) (cubeInterior Q) (fun y => w (cubeProj Q y)) x) ^ 2 =
      ∑ x ∈ Q.vertices, ∑ k : Fin d, (if x + unit k ∈ Q.vertices then
        (dirichletSolution (constCond a) (cubeInterior Q) w (x + unit k) -
          dirichletSolution (constCond a) (cubeInterior Q) w x) ^ 2 else 0) := by
  refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun k _ => ?_
  split_ifs with h
  · rw [dirichletSolution_comp_cubeProj _ Q w hx, dirichletSolution_comp_cubeProj _ Q w h]
  · have hnot : ∀ y, y ∉ Q.vertices → y ∉ cubeInterior Q := fun y hy hi =>
      hy (Finset.mem_filter.mp hi).1
    have hxint : x ∉ cubeInterior Q := fun hi => h (add_unit_mem_of_mem_cubeInterior Q hi k).1
    rw [dirichletSolution_eq_of_not_mem _ _ _ (hnot _ h),
      dirichletSolution_eq_of_not_mem _ _ _ hxint, cubeProj_add_unit_of_not_mem Q hx h,
      cubeProj_of_mem Q hx, sub_self, zero_pow two_ne_zero]

/-- The weighted squared gradient sums of the projected datum over a subset of `Q`. -/
theorem sum_weighted_sq_grad_comp_cubeProj (a : Fin d → ℝ) (Q : IntegerCube d)
    {S : Finset (Vertex d)} (hS : S ⊆ Q.vertices) (w : Vertex d → ℝ) :
    ∑ x ∈ S, ∑ k : Fin d, a k * (w (cubeProj Q (x + unit k)) - w (cubeProj Q x)) ^ 2 =
      ∑ x ∈ S, ∑ k : Fin d,
        (if x + unit k ∈ Q.vertices then a k * (w (x + unit k) - w x) ^ 2 else 0) := by
  refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun k _ => ?_
  rw [cubeProj_of_mem Q (hS hx)]
  split_ifs with h
  · rw [cubeProj_of_mem Q h]
  · rw [cubeProj_add_unit_of_not_mem Q (hS hx) h, sub_self, zero_pow two_ne_zero, mul_zero]

/-- The gradient magnitudes of the projected datum on `Q`. -/
theorem sqrt_sum_sq_grad_comp_cubeProj (Q : IntegerCube d) (w : Vertex d → ℝ) {x : Vertex d}
    (hx : x ∈ Q.vertices) :
    √(∑ k : Fin d, (w (cubeProj Q (x + unit k)) - w (cubeProj Q x)) ^ 2) =
      √(∑ k : Fin d, (if x + unit k ∈ Q.vertices then (w (x + unit k) - w x) ^ 2 else 0)) := by
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [cubeProj_of_mem Q hx]
  split_ifs with h
  · rw [cubeProj_of_mem Q h]
  · rw [cubeProj_add_unit_of_not_mem Q hx h, sub_self, zero_pow two_ne_zero]

/-- The energy of the edges inside `Q` is at most the energy of all edges from `Q`. -/
theorem innerEdgeEnergy_le_edgeEnergy (c : Edge d → ℝ) (hc0 : ∀ e, 0 ≤ c e) (Q : IntegerCube d)
    (g : Vertex d → ℝ) : innerEdgeEnergy c Q g ≤ edgeEnergy c Q.vertices g := by
  rw [edgeEnergy, Finset.sum_comm, innerEdgeEnergy]
  refine Finset.sum_le_sum fun j _ => ?_
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun x _ _ =>
    mul_nonneg (hc0 _) (sq_nonneg _)

/-- The energy of the edges inside `Q` only depends on the function on `Q`. -/
theorem innerEdgeEnergy_congr (c : Edge d → ℝ) (Q : IntegerCube d) {g g' : Vertex d → ℝ}
    (h : ∀ x ∈ Q.vertices, g x = g' x) : innerEdgeEnergy c Q g = innerEdgeEnergy c Q g' := by
  simp only [innerEdgeEnergy]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun x hx => ?_
  obtain ⟨hxQ, hxjQ⟩ := Finset.mem_filter.mp hx
  rw [h x hxQ, h _ hxjQ]

theorem mem_cornerCube_succ {M : ℕ} {i : Vertex d} (hi : i ∈ (cornerCube 0 M).vertices) :
    i ∈ (cornerCube 0 (M + 1)).vertices := by
  rw [IntegerCube.mem_vertices] at hi ⊢
  intro k
  have h := hi k
  simp only [cornerCube, Pi.zero_apply, zero_add] at h ⊢
  push_cast
  omega

theorem add_unit_mem_cornerCube_succ {M : ℕ} {i : Vertex d} (hi : i ∈ (cornerCube 0 M).vertices)
    (j : Fin d) : i + unit j ∈ (cornerCube 0 (M + 1)).vertices := by
  rw [IntegerCube.mem_vertices] at hi ⊢
  intro k
  have h := hi k
  simp only [cornerCube, Pi.zero_apply, zero_add] at h ⊢
  rw [add_unit_apply]
  push_cast
  split_ifs <;> omega

/-- **Lemma 6.3 (ii) on the edges inside `Q`.** -/
theorem innerEdgeEnergy_patch_dirichletSolution_div_le (hd : 0 < d) (a : Fin d → ℝ) {lam Λ : ℝ}
    (hlam : 0 < lam) (ha : ∀ j, lam ≤ a j ∧ a j ≤ Λ) (c : Edge d → ℝ) (hc0 : ∀ e, 0 ≤ c e)
    (hcΛ : ∀ e, c e ≤ Λ) (Q : IntegerCube d) (hL : 0 < Q.size) (w : Vertex d → ℝ)
    {r : ℕ} (hr : 0 < r) (z : Vertex d) (M : ℕ) {N : ℕ} (hN : 0 < N)
    (hsub : (cornerCube z ((M + 1) * N)).vertices ⊆ (shrinkCube Q (r + 3)).vertices)
    {D : ℕ} (hT1 : ∀ k, z k ≤ Q.corner k + D)
    (hT2 : ∀ k, Q.corner k + Q.size ≤ z k + (M * N : ℕ) + D) {ρ : ℕ} (hρ : 0 < ρ)
    (v : Vertex d → ℝ) (δ : Vertex d → ℝ) (hδ : ∀ i, 0 ≤ δ i)
    (hinner : ∀ i ∈ (cornerCube 0 M).vertices,
      innerEdgeEnergy c (cornerCube (z + (N : ℤ) • i) N) v / (N : ℝ) ^ d ≤
        ∑ k, a k * cubeSlope N (dirichletSolution (constCond a) (cubeInterior Q) w)
          (z + (N : ℤ) • i) k ^ 2 + 2 * δ i)
    (hface : ∀ i ∈ (cornerCube 0 M).vertices, ∀ j : Fin d,
      ∀ x ∈ (cornerCube (z + (N : ℤ) • i) N).upperFace j, c (x, j) ≠ 0 →
        v x = cubeAffine N (dirichletSolution (constCond a) (cubeInterior Q) w)
            (z + (N : ℤ) • i) x ∧
          v (x + unit j) = cubeAffine N (dirichletSolution (constCond a) (cubeInterior Q) w)
            (z + (N : ℤ) • i + (N : ℤ) • unit j) (x + unit j))
    {γ p : ℝ} (hγ0 : 0 < γ) (hγ : γ ≤ 1 / 16) (hp : 2 < p) (hγp : γ * (p / (p - 2)) < 1) :
    innerEdgeEnergy c Q (patch (cubeCutoff (cornerCube z (M * N)) ρ) v
        (dirichletSolution (constCond a) (cubeInterior Q) w)) / (Q.size : ℝ) ^ d ≤
      innerEdgeEnergy (constCond a) Q (dirichletSolution (constCond a) (cubeInterior Q) w) /
          (Q.size : ℝ) ^ d +
        (6 * (N : ℝ) ^ d * ∑ i ∈ (cornerCube 0 M).vertices, δ i +
          3 * (Λ * (d * (3 * ((1 + d) * 2 ^ d * (N : ℝ) ^ 3 *
            (10 * d * Λ / (lam * (r : ℝ) ^ 2)) + 1 / N) *
              ∑ x ∈ Q.vertices, ∑ k : Fin d, (if x + unit k ∈ Q.vertices then
                (dirichletSolution (constCond a) (cubeInterior Q) w (x + unit k) -
                  dirichletSolution (constCond a) (cubeInterior Q) w x) ^ 2 else 0)))) +
          6 * Λ * (d * (1 / (ρ : ℝ)) ^ 2) *
            (∑ i ∈ (cornerCube 0 M).vertices, ∑ x ∈ (cornerCube (z + (N : ℤ) • i) N).vertices,
                (v x - cubeAffine N (dirichletSolution (constCond a) (cubeInterior Q) w)
                  (z + (N : ℤ) • i) x) ^ 2 +
              ∑ i ∈ (cornerCube 0 M).vertices, ∑ x ∈ (cornerCube (z + (N : ℤ) • i) N).vertices,
                (dirichletSolution (constCond a) (cubeInterior Q) w x -
                  cubeAffine N (dirichletSolution (constCond a) (cubeInterior Q) w)
                    (z + (N : ℤ) • i) x) ^ 2)) / (Q.size : ℝ) ^ d +
        (2 + 3 * Λ / lam) *
          (2 * ((∑ x ∈ cubeLayer Q (D + ρ + N + 1), ∑ k : Fin d,
              (if x + unit k ∈ Q.vertices then a k * (w (x + unit k) - w x) ^ 2 else 0)) /
                (Q.size : ℝ) ^ d) +
            88 * Λ * Real.exp (γ + 4 * γ ^ 2) *
              ((2 * (d : ℝ)) ^ (p / (p - 2)) / (1 - γ * (p / (p - 2)))) ^ (1 - 2 / p) *
              ((((D + ρ + N : ℕ) : ℝ) + 1) / Q.size) ^ γ *
              ((∑ x ∈ Q.vertices, √(∑ k : Fin d,
                  (if x + unit k ∈ Q.vertices then (w (x + unit k) - w x) ^ 2 else 0)) ^ p) /
                (Q.size : ℝ) ^ d) ^ (2 / p)) := by
  have hV : (0 : ℝ) < (Q.size : ℝ) ^ d := by positivity
  have hagree : ∀ x ∈ Q.vertices,
      dirichletSolution (constCond a) (cubeInterior Q) (fun y => w (cubeProj Q y)) x =
        dirichletSolution (constCond a) (cubeInterior Q) w x :=
    fun x hx => dirichletSolution_comp_cubeProj _ Q w hx
  have htile : ∀ i ∈ (cornerCube 0 (M + 1)).vertices,
      ∀ x ∈ (cornerCube (z + (N : ℤ) • i) N).vertices, ∀ k : Fin d,
        x ∈ Q.vertices ∧ x + unit k ∈ Q.vertices := fun i hi x hx k =>
    add_unit_mem_of_mem_shrinkCube Q (by omega) (hsub (tile_subset z (M + 1) hi hx)) k
  have hslope : ∀ i ∈ (cornerCube 0 (M + 1)).vertices, ∀ k,
      cubeSlope N (dirichletSolution (constCond a) (cubeInterior Q) (fun y => w (cubeProj Q y)))
        (z + (N : ℤ) • i) k =
      cubeSlope N (dirichletSolution (constCond a) (cubeInterior Q) w) (z + (N : ℤ) • i) k :=
    fun i hi => cubeSlope_congr (fun x hx => hagree x (htile i hi x hx ⟨0, hd⟩).1)
      (fun x hx k => hagree _ (htile i hi x hx k).2)
  have haff : ∀ i ∈ (cornerCube 0 (M + 1)).vertices, ∀ x,
      cubeAffine N (dirichletSolution (constCond a) (cubeInterior Q) (fun y => w (cubeProj Q y)))
        (z + (N : ℤ) • i) x =
      cubeAffine N (dirichletSolution (constCond a) (cubeInterior Q) w) (z + (N : ℤ) • i) x :=
    fun i hi => cubeAffine_congr (fun x hx => hagree x (htile i hi x hx ⟨0, hd⟩).1)
      (fun x hx k => hagree _ (htile i hi x hx k).2)
  have hnext : ∀ i ∈ (cornerCube 0 M).vertices, ∀ j : Fin d,
      z + (N : ℤ) • i + (N : ℤ) • unit j = z + (N : ℤ) • (i + unit j) := fun i _ j => by
    rw [smul_add, add_assoc]
  have main := edgeEnergy_patch_dirichletSolution_div_le hd a hlam ha c hc0 hcΛ Q hL
    (fun y => w (cubeProj Q y)) hr z M hN hsub hT1 hT2 hρ v δ hδ
    (fun i hi => by
      simp only [hslope i (mem_cornerCube_succ hi)]
      exact hinner i hi)
    (fun i hi j x hx hc => by
      rw [haff i (mem_cornerCube_succ hi), hnext i hi j,
        haff _ (add_unit_mem_cornerCube_succ hi j), ← hnext i hi j]
      exact hface i hi j x hx hc)
    hγ0 hγ hp hγp
  dsimp only at main
  have hX : ∀ g : Vertex d → ℝ,
      ∑ i ∈ (cornerCube 0 M).vertices, ∑ x ∈ (cornerCube (z + (N : ℤ) • i) N).vertices,
        (g x - cubeAffine N (dirichletSolution (constCond a) (cubeInterior Q)
          (fun y => w (cubeProj Q y))) (z + (N : ℤ) • i) x) ^ 2 =
      ∑ i ∈ (cornerCube 0 M).vertices, ∑ x ∈ (cornerCube (z + (N : ℤ) • i) N).vertices,
        (g x - cubeAffine N (dirichletSolution (constCond a) (cubeInterior Q) w)
          (z + (N : ℤ) • i) x) ^ 2 := fun g =>
    Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun x _ => by
      rw [haff i (mem_cornerCube_succ hi)]
  have hY : ∑ i ∈ (cornerCube 0 M).vertices, ∑ x ∈ (cornerCube (z + (N : ℤ) • i) N).vertices,
        (dirichletSolution (constCond a) (cubeInterior Q) (fun y => w (cubeProj Q y)) x -
          cubeAffine N (dirichletSolution (constCond a) (cubeInterior Q) w)
            (z + (N : ℤ) • i) x) ^ 2 =
      ∑ i ∈ (cornerCube 0 M).vertices, ∑ x ∈ (cornerCube (z + (N : ℤ) • i) N).vertices,
        (dirichletSolution (constCond a) (cubeInterior Q) w x -
          cubeAffine N (dirichletSolution (constCond a) (cubeInterior Q) w)
            (z + (N : ℤ) • i) x) ^ 2 :=
    Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun x hx => by
      rw [hagree x (htile i (mem_cornerCube_succ hi) x hx ⟨0, hd⟩).1]
  have hH : ∑ x ∈ Q.vertices, √(∑ k : Fin d, (w (cubeProj Q (x + unit k)) -
        w (cubeProj Q x)) ^ 2) ^ p =
      ∑ x ∈ Q.vertices, √(∑ k : Fin d,
        (if x + unit k ∈ Q.vertices then (w (x + unit k) - w x) ^ 2 else 0)) ^ p :=
    Finset.sum_congr rfl fun x hx => by rw [sqrt_sum_sq_grad_comp_cubeProj Q w hx]
  rw [edgeEnergy_dirichletSolution_comp_cubeProj, sum_sq_grad_dirichletSolution_comp_cubeProj,
    hX v, hX, hY, sum_weighted_sq_grad_comp_cubeProj a Q (cubeLayer_subset _ _) w, hH] at main
  refine le_trans ?_ main
  refine div_le_div_of_nonneg_right ?_ hV.le
  rw [← innerEdgeEnergy_congr c Q (g := patch (cubeCutoff (cornerCube z (M * N)) ρ) v
    (dirichletSolution (constCond a) (cubeInterior Q) (fun y => w (cubeProj Q y)))) fun x hx => by
      simp only [patch]
      rw [hagree x hx]]
  exact innerEdgeEnergy_le_edgeEnergy c hc0 Q _

end Rigidity.Dirichlet
