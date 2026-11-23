import Rigidity.Proofs.Regularity.PlanarHarmonicComparison
import Rigidity.Proofs.Regularity.PlanarGradNormBound
import Rigidity.Proofs.Regularity.PlanarCoarseBoundTwo
import Rigidity.Proofs.Percolation.PlanarNuQuadratic

/-!
# The harmonic approximation (7.7) of the coarsened function on planar squares

Armstrong and Dario (arXiv:1609.09431v2), proof of Lemma 7.1, Steps 1 and 2, in dimension two:
almost surely, for `3^j` above a minimal scale `𝒳 ≤ O_s(θ)` and `u` harmonic on `𝒞_∞ ∩ B_R`,
`6 · 3^{j+3} ≤ R`,
`inf_{w ∈ Ā(□_j)} ‖[u]_𝒫 - w‖_{L̲²(□_j)} ≤ C 3^{-jα} inf_a ‖u - a‖_{L̲²(C_*(□_{j+3}))}`
(`planarHarmonicDistTwo_of_homogenizationError`), with `Ā(□_j)` the functions harmonic for the
lattice Laplacian on `□_j`.

The inputs are Theorem 1 in dimension two with the discrete homogenized solution, in the form
`PlanarHomogenizationErrorTwo p p'` (the statement `PlanarHomogenizationError p p'` of the
quantitative homogenization of the Dirichlet problem, copied verbatim), the minimal scales of
Proposition 2.4 (`PlanarMinimalScalesTwo p`), the density of the infinite cluster and the planar
Meyers estimate. The homogenized solution `w` on `□_{j+1}` is compared with `[u]_𝒫` on `□_j` by
`sum_sq_coarse_sub_homogenized_le`, the gradient norm of Theorem 1 is bounded by
`planarGradNormTwo_le`, and the sizes of the partition cubes are at most `3^{α' (j+1)/2}`,
`α' = min(α, 1)`, which replaces the Hölder step with the `L^{p'}` interpolation of the source.
-/

namespace Rigidity.Proofs.Regularity

open Finset MeasureTheory LatticeProb LatticeHC LatticeProb.Percolation Rigidity.External
open Rigidity.Percolation Rigidity.Dirichlet Rigidity.Proofs.S2 Rigidity.Proofs.Cluster
open scoped Classical ENNReal Matrix

variable {ω : Configuration 2}

/-- **Theorem 1 of Armstrong and Dario in dimension two, with the discrete homogenized
solution**, for the exponent `p' > 2` (the statement `PlanarHomogenizationError p p'`, copied
verbatim with `planarGradNormTwo`). -/
def PlanarHomogenizationErrorTwo (p : unitInterval) (p' : ℝ) : Prop :=
  ∃ s α C σ : ℝ, 0 < s ∧ 0 < α ∧ 0 < C ∧ 0 < σ ∧
    planarAhom p = σ • (1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
    ∃ X : Configuration 2 → ℝ, Measurable X ∧ (∀ ω, 0 ≤ X ω) ∧ IsOsBond 2 p X s C ∧
      ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ m : ℕ, X ω ≤ 3 ^ m →
        PlanarPartitionEvent ω ∧ PlanarResolved ω ⟨m, 0⟩ ∧
          ∀ u : Vertex 2 → ℝ,
            (fun x : ↥(clusterVertices ω ⟨m, 0⟩) => u x) ∈ clusterHarmonic ω ⟨m, 0⟩ →
            ∃ uHom : Vertex 2 → ℝ,
              (∀ x ∈ cubeInterior (⟨m, 0⟩ : TriadicCube 2).toIntegerCube,
                condLaplacian (constCond fun _ => (1 : ℝ)) uHom x = 0) ∧
              (∀ x ∈ clusterVertices ω ⟨m, 0⟩,
                x ∉ cubeInterior (⟨m, 0⟩ : TriadicCube 2).toIntegerCube → uHom x = u x) ∧
              innerEdgeEnergy (constCond fun _ => (1 : ℝ)) (⟨m, 0⟩ : TriadicCube 2).toIntegerCube
                  uHom / 9 ^ m ≤ C * planarGradNormTwo ω m p' u ^ 2 ∧
              (3 : ℝ) ^ (-(m : ℝ)) *
                  √((∑ x ∈ clusterVertices ω ⟨m, 0⟩, (u x - uHom x) ^ 2) / 9 ^ m) ≤
                C * (3 : ℝ) ^ (-(α * m)) * planarGradNormTwo ω m p' u

/-- The harmonic approximation (7.7) of the proof of Armstrong–Dario, Lemma 7.1, on the squares
`□_j` of the plane, almost surely on the infinite cluster above a minimal scale `𝒳 ≤ O_s(θ)`, for
the functions harmonic on `𝒞_∞ ∩ B_R`, `6 · 3^{j+3} ≤ R`. -/
def PlanarHarmonicDistTwo (p : unitInterval) : Prop :=
  ∃ s θ C₁ α : ℝ, 0 < s ∧ 0 < θ ∧ 0 ≤ C₁ ∧ 0 < α ∧
    ∃ X : Configuration 2 → ℝ, Measurable X ∧ (∀ ω, 0 ≤ X ω) ∧ IsOsBond 2 p X s θ ∧
      ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω,
        ∀ R : ℝ, ∀ u : uniqueInfiniteComponent h → ℝ,
          IsHarmonicInBall (uniqueInfiniteComponent h) R u →
          ∀ j : ℕ, X ω ≤ 3 ^ j → 6 * 3 ^ (j + 3) ≤ R →
            squareHarmonicDist j (planarCoarse (uniqueInfiniteComponent h) u) ≤
              C₁ / ((3 : ℝ) ^ j) ^ α * clusterSquareOsc (uniqueInfiniteComponent h) u (j + 3)

/-- The sum of squares from the error bound of Theorem 1. -/
theorem sum_sq_le_of_homogenizationError {m : ℕ} {S X : ℝ} (hS : 0 ≤ S)
    (h : (3 : ℝ) ^ (-(m : ℝ)) * √(S / 9 ^ m) ≤ X) : S ≤ 81 ^ m * X ^ 2 := by
  have h3 : (0 : ℝ) < 3 ^ m := by positivity
  rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, inv_mul_le_iff₀ h3] at h
  have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  rw [Real.sq_sqrt (by positivity), div_le_iff₀ (by positivity)] at hsq
  have e : ((3 : ℝ) ^ m) ^ 2 * 9 ^ m = 81 ^ m := by
    rw [← pow_mul, mul_comm m 2, pow_mul, ← mul_pow]; norm_num
  calc S ≤ (3 ^ m * X) ^ 2 * 9 ^ m := hsq
    _ = 81 ^ m * X ^ 2 := by rw [← e]; ring

/-- **(7.7) on one square** in terms of the gradient norm `M` of Theorem 1: for `w` harmonic on
the interior of `□_{i+3}` with the energy and error bounds of Theorem 1 at the scale `i + 3`,
`‖[u]_𝒫 - w‖²_{L̲²(□_{i+2})} ≤ (2 δ² 9^{i+4} C² P² + 8 · 6400 · 729 δ² C) M²`,
`P = 3^{-α(i+3)}`. -/
theorem squareL2_coarse_sub_homogenized_sq_le (hP : PlanarPartitionEvent ω) (C : OpenComponent ω)
    (u : C → ℝ) {i : ℕ} (hi : 2 ≤ i) (hres : PlanarResolved ω ⟨i + 3, 0⟩) {w : Vertex 2 → ℝ}
    (hw : ∀ x ∈ cubeInterior (⟨i + 3, 0⟩ : TriadicCube 2).toIntegerCube,
      condLaplacian (constCond fun _ => (1 : ℝ)) w x = 0) {δ : ℝ}
    (hδ : ∀ y ∈ triadicCubeFinset 2 (i + 3) 0, (3 : ℝ) ^ (planarPartCube ω y).scale ≤ δ)
    (hsmall : ∀ y ∈ triadicCubeFinset 2 (i + 2) 0, (planarPartCube ω y).scale ≤ i)
    {Ch P M : ℝ}
    (hE : innerEdgeEnergy (constCond fun _ => (1 : ℝ)) (⟨i + 3, 0⟩ : TriadicCube 2).toIntegerCube
      w / 9 ^ (i + 3) ≤ Ch * M ^ 2)
    (hL : (3 : ℝ) ^ (-((i + 3 : ℕ) : ℝ)) * √((∑ x ∈ clusterVertices ω ⟨i + 3, 0⟩,
        (Rigidity.Section3.extend C u x - w x) ^ 2) / 9 ^ (i + 3)) ≤ Ch * P * M) :
    squareL2 (i + 2) (fun y => planarCoarse C u y - w y) ^ 2 ≤
      (2 * δ ^ 2 * 9 ^ (i + 4) * Ch ^ 2 * P ^ 2 + 8 * 6400 * 729 * δ ^ 2 * Ch) * M ^ 2 := by
  have hB := sum_sq_coarse_sub_homogenized_le hP C u hi hres hw hδ hsmall
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = ∑ x ∈ clusterVertices ω ⟨i + 3, 0⟩,
      (Rigidity.Section3.extend C u x - w x) ^ 2 := ⟨_, rfl⟩
  rw [← hSdef] at hB hL
  have hS0 : 0 ≤ S := by rw [hSdef]; exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hS := sum_sq_le_of_homogenizationError hS0 hL
  obtain ⟨I, hIdef⟩ : ∃ I : ℝ, I = innerEdgeEnergy (constCond fun _ => (1 : ℝ))
      (⟨i + 3, 0⟩ : TriadicCube 2).toIntegerCube w := ⟨_, rfl⟩
  rw [← hIdef] at hB hE
  have hI0 : 0 ≤ I := by
    rw [hIdef]; unfold innerEdgeEnergy
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      mul_nonneg (by simp [constCond]) (sq_nonneg _)
  have hI : I ≤ 9 ^ (i + 3) * (Ch * M ^ 2) := by
    rwa [div_le_iff₀ (by positivity), mul_comm] at hE
  have h3i : (0 : ℝ) < 3 ^ i := by positivity
  have hG : (2 * δ * (80 / 3 ^ i * √I)) ^ 2 ≤ 4 * 6400 * 729 * δ ^ 2 * (Ch * M ^ 2) := by
    rw [mul_pow, mul_pow, mul_pow, div_pow, Real.sq_sqrt hI0]
    have e : (9 : ℝ) ^ (i + 3) = 729 * (3 ^ i) ^ 2 := by
      rw [← pow_mul, mul_comm i 2, pow_mul]; norm_num; ring
    rw [e] at hI
    calc 2 ^ 2 * δ ^ 2 * (80 ^ 2 / (3 ^ i) ^ 2 * I)
        ≤ 2 ^ 2 * δ ^ 2 * (80 ^ 2 / (3 ^ i) ^ 2 * (729 * (3 ^ i) ^ 2 * (Ch * M ^ 2))) := by
          gcongr
      _ = 4 * 6400 * 729 * δ ^ 2 * (Ch * M ^ 2) := by field_simp; ring
  unfold squareL2
  rw [Real.sq_sqrt (div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)),
    three_pow_two_mul, div_le_iff₀ (by positivity)]
  have hδ2 : 0 ≤ δ ^ 2 := sq_nonneg _
  calc ∑ y ∈ triadicCubeFinset 2 (i + 2) 0, (planarCoarse C u y - w y) ^ 2
      ≤ 2 * δ ^ 2 * S + 2 * 9 ^ (i + 2) * (2 * δ * (80 / 3 ^ i * √I)) ^ 2 := hB
    _ ≤ 2 * δ ^ 2 * (81 ^ (i + 3) * (Ch * P * M) ^ 2) +
          2 * 9 ^ (i + 2) * (4 * 6400 * 729 * δ ^ 2 * (Ch * M ^ 2)) := by
        gcongr
    _ = (2 * δ ^ 2 * 9 ^ (i + 4) * Ch ^ 2 * P ^ 2 + 8 * 6400 * 729 * δ ^ 2 * Ch) * M ^ 2 *
          9 ^ (i + 2) := by
        rw [show (81 : ℝ) ^ (i + 3) = 9 ^ (i + 4) * 9 ^ (i + 2) by
          rw [← pow_add, show (81 : ℝ) = 9 ^ 2 by norm_num, ← pow_mul]; ring_nf]
        ring

/-- The exponents of the two terms of `squareL2_coarse_sub_homogenized_sq_le` with
`δ = (3^{i+3})^{α'/2}`, `α' ≤ min(α, 1)`. -/
theorem rpow_three_bounds {α α' : ℝ} (hα'α : α' ≤ α) (hα'1 : α' ≤ 1) (hα'0 : 0 < α') (i : ℕ) :
    (((3 : ℝ) ^ (i + 3)) ^ (α' / 2)) ^ 2 * ((3 : ℝ) ^ (-(α * ((i + 3 : ℕ) : ℝ)))) ^ 2 ≤
        3 * (3 : ℝ) ^ (-(α' * ((i + 2 : ℕ) : ℝ))) ∧
      (((3 : ℝ) ^ (i + 3)) ^ (α' / 2)) ^ 2 / 9 ^ (i + 2) ≤
        3 * (3 : ℝ) ^ (-(α' * ((i + 2 : ℕ) : ℝ))) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hsq : ∀ a : ℝ, ((3 : ℝ) ^ a) ^ 2 = (3 : ℝ) ^ (2 * a) := fun a => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h3.le]; norm_num; ring_nf
  have hδ : ((3 : ℝ) ^ (i + 3)) ^ (α' / 2) = (3 : ℝ) ^ (((i : ℝ) + 3) * (α' / 2)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h3.le]; push_cast; ring_nf
  have h9 : (9 : ℝ) ^ (i + 2) = (3 : ℝ) ^ (2 * ((i : ℝ) + 2)) := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, ← pow_mul, ← Real.rpow_natCast]; push_cast; ring_nf
  have h3e : ∀ a : ℝ, 3 * (3 : ℝ) ^ a = (3 : ℝ) ^ (1 + a) := fun a => by
    rw [Real.rpow_add h3, Real.rpow_one]
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  push_cast
  rw [hδ, hsq, hsq, ← Real.rpow_add h3, h3e, h9, ← Real.rpow_sub h3]
  have hm1 := mul_le_mul_of_nonneg_left hα'α (by linarith : (0 : ℝ) ≤ (i : ℝ) + 3)
  have hm2 := mul_le_mul_of_nonneg_left hα'1 (by linarith : (0 : ℝ) ≤ 2 * (i : ℝ) + 5)
  constructor
  · apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith
  · apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith

/-- The combination of the bounds: `x² ≤ A M²`, `0 ≤ M ≤ B Γ` and `A B² ≤ K² Q` give
`x ≤ K √Q Γ`. -/
theorem le_of_sq_le_mul_sq {x A M B Γ K Q : ℝ} (hx0 : 0 ≤ x) (hA : 0 ≤ A) (hM0 : 0 ≤ M)
    (hΓ : 0 ≤ Γ) (hK : 0 ≤ K) (hQ : 0 ≤ Q) (hx : x ^ 2 ≤ A * M ^ 2) (hMB : M ≤ B * Γ)
    (hAB : A * B ^ 2 ≤ K ^ 2 * Q) : x ≤ K * √Q * Γ := by
  have hM2 : M ^ 2 ≤ (B * Γ) ^ 2 := pow_le_pow_left₀ hM0 hMB 2
  have h1 : x ^ 2 ≤ (K * √Q * Γ) ^ 2 := by
    calc x ^ 2 ≤ A * M ^ 2 := hx
      _ ≤ A * (B * Γ) ^ 2 := mul_le_mul_of_nonneg_left hM2 hA
      _ = A * B ^ 2 * Γ ^ 2 := by ring
      _ ≤ K ^ 2 * Q * Γ ^ 2 := mul_le_mul_of_nonneg_right hAB (sq_nonneg _)
      _ = (K * √Q * Γ) ^ 2 := by rw [mul_pow, mul_pow, Real.sq_sqrt hQ]
  exact (pow_le_pow_iff_left₀ hx0 (by positivity) two_ne_zero).1 h1

theorem sqrt_three_rpow_neg (α' : ℝ) (j : ℕ) :
    √((3 : ℝ) ^ (-(α' * (j : ℝ)))) = 1 / ((3 : ℝ) ^ j) ^ (α' / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num), eq_div_iff (by positivity), ← Real.rpow_add (by norm_num)]
  convert Real.rpow_zero (3 : ℝ) using 2
  ring

/-- The constant of (7.7) from the two terms of `squareL2_coarse_sub_homogenized_sq_le`. -/
theorem coeff_le_of_bounds {d P Q Ch c : ℝ} {i : ℕ} (hCh : 0 ≤ Ch) (hb1 : d * P ^ 2 ≤ 3 * Q)
    (hb2 : d / 9 ^ (i + 2) ≤ 3 * Q) :
    (2 * d * 9 ^ (i + 4) * Ch ^ 2 * P ^ 2 + 8 * 6400 * 729 * d * Ch) * (4 * c / 3 ^ (i + 2)) ^ 2 ≤
      16 * c ^ 2 * 3 * (162 * Ch ^ 2 + 8 * 6400 * 729 * Ch) * Q := by
  have e : (2 * d * 9 ^ (i + 4) * Ch ^ 2 * P ^ 2 + 8 * 6400 * 729 * d * Ch) *
      (4 * c / 3 ^ (i + 2)) ^ 2 =
      16 * c ^ 2 * (162 * Ch ^ 2 * (d * P ^ 2) + 8 * 6400 * 729 * Ch * (d / 9 ^ (i + 2))) := by
    have h9 : (9 : ℝ) ^ (i + 4) = 81 * 9 ^ (i + 2) := by ring
    have h3 : ((3 : ℝ) ^ (i + 2)) ^ 2 = 9 ^ (i + 2) := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [div_pow, mul_pow, h9, h3]
    field_simp
    ring
  rw [e]
  have hc2 : 0 ≤ 16 * c ^ 2 := by positivity
  calc 16 * c ^ 2 * (162 * Ch ^ 2 * (d * P ^ 2) + 8 * 6400 * 729 * Ch * (d / 9 ^ (i + 2)))
      ≤ 16 * c ^ 2 * (162 * Ch ^ 2 * (3 * Q) + 8 * 6400 * 729 * Ch * (3 * Q)) := by
        gcongr
    _ = 16 * c ^ 2 * 3 * (162 * Ch ^ 2 + 8 * 6400 * 729 * Ch) * Q := by ring

theorem squareHarmonicDist_le_squareL2 {j : ℕ} {g w : Vertex 2 → ℝ} (hw : w ∈ squareHarmonic j) :
    squareHarmonicDist j g ≤ squareL2 j (fun y => g y - w y) :=
  ciInf_le (f := fun F : squareHarmonic j => squareL2 j (g - F))
    ⟨0, fun _ ⟨_, hF⟩ => hF ▸ squareL2_nonneg _ _⟩ ⟨w, hw⟩

/-- **(7.7) on one square** from Theorem 1 at the scale `i + 3`: for `w` harmonic on the interior
of `□_{i+3}` with the energy and error bounds of Theorem 1, partition cubes of side at most
`(3^{i+3})^{α'/2}`, `α' ≤ min(α, 1)`, and the bound `M ≤ 4 c 3^{-(i+2)} ‖u - a‖` of the gradient
norm for every `a`, `inf_w ‖[u]_𝒫 - w‖_{L̲²(□_{i+2})} ≤ K 3^{-(i+2)α'/2} Γ_{i+5}`. -/
theorem squareHarmonicDist_le_of_theoremOne {ω : Configuration 2} (hP : PlanarPartitionEvent ω)
    (C : OpenComponent ω) (u : C → ℝ) {i : ℕ} (hi : 2 ≤ i) (hres : PlanarResolved ω ⟨i + 3, 0⟩)
    {w : Vertex 2 → ℝ}
    (hw : ∀ x ∈ cubeInterior (⟨i + 3, 0⟩ : TriadicCube 2).toIntegerCube,
      condLaplacian (constCond fun _ => (1 : ℝ)) w x = 0) {α α' : ℝ} (hα'α : α' ≤ α)
    (hα'1 : α' ≤ 1) (hα'0 : 0 < α')
    (hδ : ∀ y ∈ triadicCubeFinset 2 (i + 3) 0,
      (3 : ℝ) ^ (planarPartCube ω y).scale ≤ ((3 : ℝ) ^ (i + 3)) ^ (α' / 2))
    (hsmall : ∀ y ∈ triadicCubeFinset 2 (i + 2) 0, (planarPartCube ω y).scale ≤ i)
    {Ch c M : ℝ} (hCh : 0 ≤ Ch) (hM0 : 0 ≤ M)
    (hE : innerEdgeEnergy (constCond fun _ => (1 : ℝ)) (⟨i + 3, 0⟩ : TriadicCube 2).toIntegerCube
      w / 9 ^ (i + 3) ≤ Ch * M ^ 2)
    (hL : (3 : ℝ) ^ (-((i + 3 : ℕ) : ℝ)) * √((∑ x ∈ clusterVertices ω ⟨i + 3, 0⟩,
        (Rigidity.Section3.extend C u x - w x) ^ 2) / 9 ^ (i + 3)) ≤
      Ch * (3 : ℝ) ^ (-(α * ((i + 3 : ℕ) : ℝ))) * M)
    (hMb : ∀ a : ℝ, M ≤ 4 * c / 3 ^ (i + 2) *
      clusterSquareL2 ω (i + 2 + 3) (fun x => Rigidity.Section3.extend C u x - a)) :
    squareHarmonicDist (i + 2) (planarCoarse C u) ≤
      √(16 * c ^ 2 * 3 * (162 * Ch ^ 2 + 8 * 6400 * 729 * Ch)) / ((3 : ℝ) ^ (i + 2)) ^ (α' / 2) *
        clusterSquareOsc C u (i + 2 + 3) := by
  have hsq := squareL2_coarse_sub_homogenized_sq_le hP C u hi hres hw hδ hsmall hE hL
  obtain ⟨hb1, hb2⟩ := rpow_three_bounds hα'α hα'1 hα'0 i
  have hcoef := coeff_le_of_bounds (c := c) hCh hb1 hb2
  have hK0 : 0 ≤ √(16 * c ^ 2 * 3 * (162 * Ch ^ 2 + 8 * 6400 * 729 * Ch)) := Real.sqrt_nonneg _
  have hD := squareHarmonicDist_le_squareL2 (g := planarCoarse C u)
    (mem_squareHarmonic_of_cubeInterior hw)
  have hall : ∀ a : ℝ, squareHarmonicDist (i + 2) (planarCoarse C u) ≤
      √(16 * c ^ 2 * 3 * (162 * Ch ^ 2 + 8 * 6400 * 729 * Ch)) *
        (1 / ((3 : ℝ) ^ (i + 2)) ^ (α' / 2)) *
        clusterSquareL2 ω (i + 2 + 3) (fun x => Rigidity.Section3.extend C u x - a) := by
    intro a
    refine hD.trans ?_
    rw [← sqrt_three_rpow_neg]
    refine le_of_sq_le_mul_sq (squareL2_nonneg _ _) (by positivity) hM0
      (clusterSquareL2_nonneg _ _ _) hK0 (by positivity) hsq (hMb a) ?_
    rw [Real.sq_sqrt (by positivity)]
    exact hcoef
  have hK' : 0 ≤ √(16 * c ^ 2 * 3 * (162 * Ch ^ 2 + 8 * 6400 * 729 * Ch)) *
      (1 / ((3 : ℝ) ^ (i + 2)) ^ (α' / 2)) := by positivity
  rw [clusterSquareOsc, div_eq_mul_one_div _ (((3 : ℝ) ^ (i + 2)) ^ (α' / 2)),
    Real.mul_iInf_of_nonneg hK']
  exact le_ciInf hall

/-- **The harmonic approximation (7.7) on planar squares almost surely**, from Theorem 1 in
dimension two with the discrete homogenized solution and the minimal scales of Proposition 2.4. -/
theorem planarHarmonicDistTwo_of_homogenizationError {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hM5 : PlanarMinimalScalesTwo p)
    (hHE : ∀ p' : ℝ, 2 < p' → PlanarHomogenizationErrorTwo p p') : PlanarHarmonicDistTwo p := by
  obtain ⟨s₃, θ₃, hs₃, hθ₃, M₃, hM₃m, hM₃0, hM₃os, hM₃ae⟩ :=
    planarPartitionSizeScale_of_minimalScales hM5
  obtain ⟨A₀, sc, hcellae, hmoms⟩ := hM5
  obtain ⟨ε, hε, t, ht, hMK⟩ := planar_meyers_rh_uniform A₀
  have hq : 1 < 1 + ε / 2 := by linarith
  obtain ⟨K₁, r₁, θ₁, hK₁, hr₁, hθ₁, M₁, hM₁m, hM₁0, hM₁os, hM₁ae⟩ :=
    hmoms t ht (1 / 2) (by norm_num)
  obtain ⟨CM, hCM, hMey⟩ := hMK K₁ hK₁
  obtain ⟨sh, αh, Ch, σ, hsh, hαh, hCh, -, -, Xh, hXhm, hXh0, hXhos, hXhae⟩ :=
    hHE (2 * (1 + ε / 2)) (by linarith)
  obtain ⟨α', hα'def⟩ : ∃ a : ℝ, a = min αh 1 := ⟨_, rfl⟩
  have hα'0 : 0 < α' := by rw [hα'def]; exact lt_min hαh one_pos
  have hα'α : α' ≤ αh := by rw [hα'def]; exact min_le_left _ _
  have hα'1 : α' ≤ 1 := by rw [hα'def]; exact min_le_right _ _
  obtain ⟨K₆, r₆, θ₆, -, hr₆, hθ₆, M₆, hM₆m, hM₆0, hM₆os, hM₆ae⟩ :=
    hmoms 1 one_pos (α' / 2) (by positivity)
  have hθp : 0 < theta 2 p := Rigidity.Percolation.theta_pos_of_criticalProbability_lt 2 p hpc
  obtain ⟨s₄, θ₄, hs₄, hθ₄, hcube⟩ := exists_clusterCubeDensity_of_concentration (d := 2) le_rfl p
    (cluster_density_concentration 2 le_rfl p hpc hp1) 1
  obtain ⟨M₄, hM₄m, hM₄0, hM₄os, hM₄ae⟩ := hcube 0
  -- the minimal scale
  obtain ⟨θa, hθa, ha⟩ := exists_isOsBond_max hsh hr₁ hCh hθ₁ hXhm hM₁m hXhos hM₁os
  obtain ⟨θb, hθb, hb⟩ := exists_isOsBond_max hs₃ hs₄ hθ₃ hθ₄ hM₃m hM₄m hM₃os hM₄os
  obtain ⟨θc, hθc, hc⟩ := exists_isOsBond_max hr₆ hr₆ hθ₆ (by positivity) hM₆m measurable_const
    hM₆os (isOsBond_const (p := p) (d := 2) (by norm_num : (0 : ℝ) < 2187) hr₆)
  obtain ⟨θab, hθab, hab⟩ := exists_isOsBond_max (lt_min hsh hr₁) (lt_min hs₃ hs₄) hθa hθb
    (hXhm.max hM₁m) (hM₃m.max hM₄m) ha hb
  obtain ⟨θX, hθX, hXos⟩ := exists_isOsBond_max (lt_min (lt_min hsh hr₁) (lt_min hs₃ hs₄))
    (lt_min hr₆ hr₆) hθab hθc ((hXhm.max hM₁m).max (hM₃m.max hM₄m))
    (hM₆m.max measurable_const) hab hc
  -- the constant
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = √(16 * (CM ^ (1 / (2 * (1 + ε / 2)))) ^ 2 * 3 *
      (162 * Ch ^ 2 + 8 * 6400 * 729 * Ch)) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hKdef]; exact Real.sqrt_nonneg _
  refine ⟨_, θX, K, α' / 2, lt_min (lt_min (lt_min hsh hr₁) (lt_min hs₃ hs₄)) (lt_min hr₆ hr₆),
    hθX, hK0, by positivity, _, ((hXhm.max hM₁m).max (hM₃m.max hM₄m)).max
      (hM₆m.max measurable_const),
    fun ω => (hXh0 ω).trans ((le_max_left _ _).trans ((le_max_left _ _).trans
      (le_max_left _ _))), hXos, ?_⟩
  filter_upwards [hcellae, hM₁ae, hM₃ae, hM₄ae, hM₆ae, hXhae, ae_planarPartitionEvent hpc] with
    ω hcells hω₁ hω₃ hω₄ hω₆ hωh hP h R u hu j hj hjR
  obtain ⟨hcell, hnb, hrh⟩ := hcells
  have hinf := uniqueInfiniteComponent_infinite h
  have hjh : Xh ω ≤ 3 ^ j :=
    ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))).trans hj
  have hj1 : M₁ ω ≤ 3 ^ j :=
    ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _))).trans hj
  have hj3 : M₃ ω ≤ 3 ^ j :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _))).trans hj
  have hj4 : M₄ ω ≤ 3 ^ j :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _))).trans hj
  have hj6 : M₆ ω ≤ 3 ^ j := ((le_max_left _ _).trans (le_max_right _ _)).trans hj
  have hj7 : (2187 : ℝ) ≤ 3 ^ j := ((le_max_right _ _).trans (le_max_right _ _)).trans hj
  have hj7' : 7 ≤ j := by
    have : (3 : ℝ) ^ 7 ≤ 3 ^ j := by norm_num; exact hj7
    exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).1 this
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
  have hi : 2 ≤ i := by omega
  have hle : ∀ m, i + 2 ≤ m → (3 : ℝ) ^ (i + 2) ≤ 3 ^ m := fun m hm =>
    pow_le_pow_right₀ (by norm_num) hm
  have hres : ∀ m, i + 2 ≤ m → PlanarResolved ω ⟨m, 0⟩ := by
    intro m hm z hz
    have hz' : z ∈ triadicCubeFinset 2 m 0 := mem_square_iff_int.2 (mem_triadicCube_zero_iff.1 hz)
    have := hω₃ m (hj3.trans (hle m hm)) z hz'
    show (planarPartCube ω z).scale ≤ m
    omega
  have hκ : 0 < theta 2 p / 2 := by positivity
  have hsub : ∀ m, i + 2 ≤ m → ∀ x ∈ clusterVertices ω ⟨m, 0⟩,
      x ∈ (uniqueInfiniteComponent h).supp := by
    intro m hm x hx
    obtain ⟨x₀, hx₀⟩ := exists_mem_square_of_clusterCubeDensity (uniqueInfiniteComponent h) hκ
      (hω₄ h) (hj4.trans (hle m hm))
    exact mem_supp_of_mem_clusterVertices hP (hres m hm) _ hinf
      (mem_triadicCube_zero_iff.2 (mem_square_iff_int.1 hx₀)) x₀.2 hx
  have hsucc : ∀ m, i + 2 ≤ m → ∀ x ∈ triadicCubeFinset 2 m 0,
      x ∈ (uniqueInfiniteComponent h).supp → x ∈ clusterVertices ω ⟨m + 1, 0⟩ :=
    fun m hm x hx hxC => mem_clusterVertices_succ hP _ hinf (hω₃ m (hj3.trans (hle m hm))) hx hxC
  have hincl : ∀ m n, i + 2 ≤ m → m < n →
      clusterVertices ω ⟨m, 0⟩ ⊆ clusterVertices ω ⟨n, 0⟩ := by
    intro m n hm hmn x hx
    have hxC := hsub m hm x hx
    have hx1 : x ∈ triadicCubeFinset 2 (n - 1) 0 := by
      have := mem_square_of_mem_clusterVertices hx
      rw [mem_square_iff_int] at this ⊢
      intro k
      have h := this k
      have h3 : (3 : ℤ) ^ m ≤ 3 ^ (n - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
    have := hsucc (n - 1) (by omega) x hx1 hxC
    rwa [show n - 1 + 1 = n by omega] at this
  have hjR' : 2 * 3 ^ (i + 3 + 3) ≤ R := by
    have e : (2 : ℝ) * 3 ^ (i + 3 + 3) = 6 * 3 ^ (i + 2 + 3) := by ring
    rw [e]; exact hjR
  have hharm6 := harm_on_square_of_isHarmonicInBall hu hjR'
  have hharm5 : ∀ (x : Vertex 2) (hx : x ∈ (uniqueInfiniteComponent h).supp),
      x ∈ triadicCubeFinset 2 (i + 2 + 3) 0 →
        componentLaplacian (uniqueInfiniteComponent h) u ⟨x, hx⟩ = 0 := by
    intro x hx hxs
    refine hharm6 x hx ?_
    rw [mem_square_iff_int] at hxs ⊢
    intro k
    have := hxs k
    have h3 : (3 : ℤ) ^ (i + 2 + 3) ≤ 3 ^ (i + 3 + 3) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  -- the scales of the partition cubes
  have hsc : ∀ x ∈ triadicCubeFinset 2 (i + 2 + 3) 0, (planarPartCube ω x).scale ≤ i + 2 :=
    fun x hx => by
      have := two_mul_le_of_three_pow_le_rpow_half
        ((hω₁ (i + 2 + 3) (hj1.trans (hle _ (by omega)))).2.2.2.1 x (mem_cube_of_mem_square hx))
      omega
  have hsmall : ∀ y ∈ triadicCubeFinset 2 (i + 2) 0, (planarPartCube ω y).scale ≤ i :=
    fun y hy => by
      have := two_mul_le_of_three_pow_le_rpow_half
        ((hω₁ (i + 2) (hj1.trans (hle _ le_rfl))).2.2.2.1 y (mem_cube_of_mem_square hy))
      omega
  have hδ : ∀ y ∈ triadicCubeFinset 2 (i + 3) 0,
      (3 : ℝ) ^ (planarPartCube ω y).scale ≤ ((3 : ℝ) ^ (i + 3)) ^ (α' / 2) := fun y hy =>
    (hω₆ (i + 3) (hj6.trans (hle _ (by omega)))).2.2.2.1 y (mem_cube_of_mem_square hy)
  have hin : ∀ x, x ∈ (uniqueInfiniteComponent h).supp → (∀ k, 2 * |x k| < 17 * 3 ^ (i + 2)) →
      x ∈ clusterVertices ω ⟨i + 2 + 3, 0⟩ := fun x hxC hx =>
    mem_clusterVertices_inner hP _ hinf hsc hxC hx
  -- the Meyers estimate
  have hω₁' := hω₁ (i + 3 + 1) (hj1.trans (hle _ (by omega)))
  have hsize : ∀ z ∈ cube (i + 3 + 1) (0 : Vertex 2), sc ω z ≤ i + 3 + 1 := fun z hz => by
    have := two_mul_le_of_three_pow_le_rpow_half (hω₁'.2.1 z hz)
    omega
  have hMeyj := meyers_on_square hMey hP (uniqueInfiniteComponent h) u
    (hres (i + 3 + 2) (by omega)) (hsub (i + 3 + 2) (by omega)) hharm6 (sc ω) hcell hnb hrh hsize
    (hω₁ (i + 3) (hj1.trans (hle _ (by omega)))).1
  -- Theorem 1 at the scale `i + 3`
  obtain ⟨-, -, hfun⟩ := hωh (i + 3) (hjh.trans (hle _ (by omega)))
  have hharm3 := clusterRestrictTo_mem_clusterHarmonic hP (hres (i + 3) (by omega))
    (uniqueInfiniteComponent h) (hsub (i + 3) (by omega)) fun x hx hxV _ => by
      refine hharm6 x hx ?_
      have := mem_square_of_mem_clusterVertices hxV
      rw [mem_square_iff_int] at this ⊢
      intro k
      have h1 := this k
      have h3 : (3 : ℤ) ^ (i + 3) ≤ 3 ^ (i + 3 + 3) := pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
  obtain ⟨w, hw, -, hE, hL⟩ := hfun (Rigidity.Section3.extend (uniqueInfiniteComponent h) u) hharm3
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = planarGradNormTwo ω (i + 3) (2 * (1 + ε / 2))
      (Rigidity.Section3.extend (uniqueInfiniteComponent h) u) := ⟨_, rfl⟩
  rw [← hMdef] at hE hL
  have hM0 : 0 ≤ M := by
    rw [hMdef]; unfold planarGradNormTwo
    exact Real.rpow_nonneg (div_nonneg (Finset.sum_nonneg fun _ _ =>
      Real.rpow_nonneg (gradNormIn_nonneg _ _ _ _) _) (by positivity)) _
  have hMb : ∀ a : ℝ, M ≤ 4 * CM ^ (1 / (2 * (1 + ε / 2))) / 3 ^ (i + 2) *
      clusterSquareL2 ω (i + 2 + 3)
        (fun x => Rigidity.Section3.extend (uniqueInfiniteComponent h) u x - a) := by
    intro a
    have hMb := planarGradNormTwo_le (uniqueInfiniteComponent h) u (j := i + 2)
      (hincl _ _ (by omega) (by omega)) (hsub (i + 2 + 3) (by omega)) hin hharm5 hq hCM hMeyj a
    rw [hMdef]
    exact hMb
  have hfin := squareHarmonicDist_le_of_theoremOne hP (uniqueInfiniteComponent h) u hi
    (hres (i + 3) (by omega)) hw hα'α hα'1 hα'0 hδ hsmall hCh.le hM0 hE hL hMb
  rw [← hKdef] at hfin
  exact hfin

end Rigidity.Proofs.Regularity
