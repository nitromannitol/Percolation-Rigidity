import Rigidity.Proofs.Dirichlet.HardyCube
import Rigidity.Proofs.Dirichlet.BoundaryLayer

/-!
# Energy of the homogenized solution in a boundary layer

For the discrete Dirichlet problem with constant conductances on an integer cube `Q` (harmonic on
the points off the extreme slices, equal to the data `f` elsewhere), the weighted energy estimate
with the Hardy weight `W_Q` of the cube bounds the energy of `u − f` in the boundary layer of
width `ℓ + 1` by `22/w(ℓ)` times the `W_Q`-weighted energy of `f`, where `w(ℓ) ≃ (ℓ + 1)^{-γ}`.
Since `W_Q ≃ dist(·, ∂Q)^{-γ}` has bounded moments of order `q < 1/γ`, Hölder's inequality then
makes this energy small when `ℓ ≪ N` and `∇f` has a higher moment.

This replaces the global Meyers estimate used for the homogenized solution in the proof of
Armstrong–Dario, Lemma 6.3, Step 3 ((6.43) and (6.44)), in the discrete route.
-/

open Finset LatticeProb LatticeHC

namespace Rigidity.Dirichlet

open Rigidity.Percolation LatticeProb.Percolation

variable {d : ℕ}

/-- The points of `Q` off the two extreme slices in every direction. -/
noncomputable def cubeInterior (Q : IntegerCube d) : Finset (Vertex d) :=
  Q.vertices.filter fun x => ∀ k, Q.corner k + 1 ≤ x k ∧ x k + 2 ≤ Q.corner k + Q.size

theorem hardyWeight_antitone {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ < 1) {s t : ℕ} (hst : s ≤ t) :
    hardyWeight γ t ≤ hardyWeight γ s := by
  induction hst with
  | refl => exact le_rfl
  | step _ ih => exact (hardyWeight_succ_le hγ0 hγ _).trans ih

/-- **Layer bound from the weighted energy estimate**: under the hypotheses of
`sum_weighted_energy_le`, on a set `T ⊆ Q` where all edge averages of `W` are at least `θ > 0`,
the energy of `φ` is at most `11/θ` times the weighted energy of `f`. -/
theorem sum_energy_le_of_weight_ge (a : Fin d → ℝ) (ha : ∀ k, 0 < a k) (W : Vertex d → ℝ)
    (hW : ∀ x, 0 < W x) {U Q T : Finset (Vertex d)} (hUQ : U ⊆ Q) (hTQ : T ⊆ Q)
    (hUk : ∀ y ∈ U, ∀ k : Fin d, y - unit k ∈ Q) {κ : ℝ} (hκ0 : 0 < κ) (hκ : κ ≤ 1 / 4)
    (hR : ∀ k : Fin d, ∀ x ∈ U, (W (x + unit k) - W x) ^ 2 / ((W x + W (x + unit k)) / 2) +
      (W x - W (x - unit k)) ^ 2 / ((W (x - unit k) + W x) / 2) ≤
        κ * (W (x + unit k) + W (x - unit k) - 2 * W x))
    (f φ : Vertex d → ℝ) (hφ : ∀ x, x ∉ U → φ x = 0)
    (hu : ∀ x ∈ U, condLaplacian (constCond a) (f + φ) x = 0) {θ : ℝ} (hθ : 0 < θ)
    (hT : ∀ x ∈ T, ∀ k : Fin d, θ ≤ (W x + W (x + unit k)) / 2) :
    ∑ x ∈ T, ∑ k : Fin d, a k * (φ (x + unit k) - φ x) ^ 2 ≤
      11 / θ * ∑ x ∈ Q, ∑ k : Fin d,
        a k * ((W x + W (x + unit k)) / 2 * (f (x + unit k) - f x) ^ 2) := by
  have hmain := sum_weighted_energy_le a ha W hW hUQ hUk hκ0 hκ hR f φ hφ hu
  have hlow : θ * ∑ x ∈ T, ∑ k : Fin d, a k * (φ (x + unit k) - φ x) ^ 2 ≤
      ∑ x ∈ Q, ∑ k : Fin d, a k * ((W x + W (x + unit k)) / 2 * (φ (x + unit k) - φ x) ^ 2) := by
    rw [Finset.mul_sum]
    refine le_trans (Finset.sum_le_sum fun x hx => ?_) (Finset.sum_le_sum_of_subset_of_nonneg hTQ
      fun x _ _ => Finset.sum_nonneg fun k _ => mul_nonneg (ha k).le
        (mul_nonneg (by have := hW x; have := hW (x + unit k); positivity) (sq_nonneg _)))
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    have := mul_le_mul_of_nonneg_right (hT x hx k)
      (mul_nonneg (ha k).le (sq_nonneg (φ (x + unit k) - φ x)))
    nlinarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hθ]
  linarith

/-- **Energy of the homogenized solution in a boundary layer.** For `0 < γ ≤ 1/16`, constant
conductances `a_k > 0`, `d ≥ 1`, and `u` harmonic on `cubeInterior Q` with `u = f` elsewhere,
`Σ_{x ∈ layer} Σ_k a_k (∇_k u)² ≤ 2 Σ_{x ∈ layer} Σ_k a_k (∇_k f)² +
  44/w(ℓ) Σ_{x∈Q} Σ_k a_k W̄_k(x) (∇_k f)²`, with `layer = cubeLayer Q (ℓ + 1)`. -/
theorem sum_energy_cubeLayer_le {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ ≤ 1 / 16) (hd : 0 < d)
    (a : Fin d → ℝ) (ha : ∀ k, 0 < a k) (Q : IntegerCube d) (u f : Vertex d → ℝ)
    (hu : ∀ x ∈ cubeInterior Q, condLaplacian (constCond a) u x = 0)
    (huf : ∀ x, x ∉ cubeInterior Q → u x = f x) (ℓ : ℕ) :
    ∑ x ∈ cubeLayer Q (ℓ + 1), ∑ k : Fin d, a k * (u (x + unit k) - u x) ^ 2 ≤
      2 * ∑ x ∈ cubeLayer Q (ℓ + 1), ∑ k : Fin d, a k * (f (x + unit k) - f x) ^ 2 +
        44 / hardyWeight γ ℓ * ∑ x ∈ Q.vertices, ∑ k : Fin d, a k *
          ((cubeHardyWeight γ Q x + cubeHardyWeight γ Q (x + unit k)) / 2 *
            (f (x + unit k) - f x) ^ 2) := by
  classical
  have hγ1 : γ < 1 := by linarith
  set W := cubeHardyWeight γ Q
  have hW : ∀ x, 0 < W x := cubeHardyWeight_pos hγ1 hd Q
  set U := cubeInterior Q
  have hUQ : U ⊆ Q.vertices := Finset.filter_subset _ _
  have hUk : ∀ y ∈ U, ∀ k : Fin d, y - unit k ∈ Q.vertices := by
    intro y hy k
    obtain ⟨hyQ, hy'⟩ := Finset.mem_filter.mp hy
    rw [IntegerCube.mem_vertices] at hyQ ⊢
    intro j
    rw [sub_unit_apply]
    have := hy' j
    split_ifs <;> constructor <;> linarith [(hyQ j).1, (hyQ j).2]
  have hR : ∀ k : Fin d, ∀ x ∈ U, (W (x + unit k) - W x) ^ 2 / ((W x + W (x + unit k)) / 2) +
      (W x - W (x - unit k)) ^ 2 / ((W (x - unit k) + W x) / 2) ≤
        4 * γ * (W (x + unit k) + W (x - unit k) - 2 * W x) := by
    intro k x hx
    have h := (Finset.mem_filter.mp hx).2 k
    exact cubeHardyWeight_ratio_add_le hγ0 hγ Q k h.1 h.2
  set φ : Vertex d → ℝ := fun x => u x - f x
  have hφ : ∀ x, x ∉ U → φ x = 0 := fun x hx => by simp [φ, huf x hx]
  have hfφ : f + φ = u := by
    funext x
    simp [φ]
  have hu' : ∀ x ∈ U, condLaplacian (constCond a) (f + φ) x = 0 := by
    rw [hfφ]
    exact hu
  -- the weight is at least `w(ℓ)` on the layer
  have hTQ : cubeLayer Q (ℓ + 1) ⊆ Q.vertices := cubeLayer_subset Q (ℓ + 1)
  have hθ : 0 < hardyWeight γ ℓ / 2 := by have := hardyWeight_pos hγ1 ℓ; positivity
  have hT : ∀ x ∈ cubeLayer Q (ℓ + 1), ∀ k : Fin d,
      hardyWeight γ ℓ / 2 ≤ (W x + W (x + unit k)) / 2 := by
    intro x hx k
    obtain ⟨hxQ, i, hi⟩ := Finset.mem_filter.mp hx
    rw [IntegerCube.mem_vertices] at hxQ
    have hWx : hardyWeight γ ℓ ≤ W x := by
      have h1 : hardyWeight γ ℓ ≤ cubeHardyWeightDir γ Q i x := by
        unfold cubeHardyWeightDir
        rcases hi with hi | hi
        · have := hardyWeight_antitone hγ0.le hγ1 (s := (x i - Q.corner i).toNat) (t := ℓ)
            (by omega)
          linarith [hardyWeight_pos hγ1 (Q.corner i + Q.size - 1 - x i).toNat]
        · have := hardyWeight_antitone hγ0.le hγ1
            (s := (Q.corner i + Q.size - 1 - x i).toNat) (t := ℓ) (by omega)
          linarith [hardyWeight_pos hγ1 (x i - Q.corner i).toNat]
      exact h1.trans (Finset.single_le_sum (f := fun j => cubeHardyWeightDir γ Q j x)
        (fun j _ => (cubeHardyWeightDir_pos hγ1 Q j x).le) (Finset.mem_univ i))
    have := hW (x + unit k)
    linarith
  have hlayer := sum_energy_le_of_weight_ge a ha W hW hUQ hTQ hUk (by positivity)
    (by linarith) hR f φ hφ hu' hθ hT
  -- `∇u = ∇f + ∇φ`
  have hsplit : ∑ x ∈ cubeLayer Q (ℓ + 1), ∑ k : Fin d, a k * (u (x + unit k) - u x) ^ 2 ≤
      2 * ∑ x ∈ cubeLayer Q (ℓ + 1), ∑ k : Fin d, a k * (f (x + unit k) - f x) ^ 2 +
        2 * ∑ x ∈ cubeLayer Q (ℓ + 1), ∑ k : Fin d, a k * (φ (x + unit k) - φ x) ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun k _ => ?_
    have hk := (ha k).le
    have e : u (x + unit k) - u x = (f (x + unit k) - f x) + (φ (x + unit k) - φ x) := by
      simp only [φ]
      ring
    rw [e]
    nlinarith [mul_nonneg hk (sq_nonneg ((f (x + unit k) - f x) - (φ (x + unit k) - φ x)))]
  have h44 : 2 * (11 / (hardyWeight γ ℓ / 2)) = 44 / hardyWeight γ ℓ := by
    have := (hardyWeight_pos hγ1 ℓ).ne'
    field_simp
    ring
  calc _ ≤ _ := hsplit
    _ ≤ 2 * ∑ x ∈ cubeLayer Q (ℓ + 1), ∑ k : Fin d, a k * (f (x + unit k) - f x) ^ 2 +
          2 * (11 / (hardyWeight γ ℓ / 2) * ∑ x ∈ Q.vertices, ∑ k : Fin d, a k *
            ((W x + W (x + unit k)) / 2 * (f (x + unit k) - f x) ^ 2)) := by
        linarith
    _ = _ := by rw [← mul_assoc, h44]

end Rigidity.Dirichlet
