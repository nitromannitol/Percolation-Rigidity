import Rigidity.Proofs.Green.CoarseIsoperimetry
import Rigidity.Proofs.Green.ClusterIsoperimetry
import Rigidity.Proofs.Percolation.WellConnected

/-!
# Cluster isoperimetry from well-connected cubes

Let `θ = 1/(10d)²`. Almost surely the cube `y + Q_{2R}` is well-connected for all large `R`
(Borel-Cantelli and Proposition 2.3, `Rigidity.Percolation.wellConnected_input`), so every cube
`z + Q_M` of radius `M = ⌈(2R)^θ⌉` meeting it is a good subcube. Since `M ≤ (2R)/100 + 1`, the
cubes with `z ∈ y + Q_{R+M+1}` are among them, and `CoarseIsoperimetry.lean` gives, under the
isoperimetric inequality of `ℤ^d`, the isoperimetric inequality of the infinite cluster in
`y + Q_R` with constant `1/(4d(2M+1)^d) ≥ R^{-θd}/(4d 10^d)`, for all nonempty sets: this is
`ClusterIsoperimetry d p 0 (θ d)` (`clusterIsoperimetry_of_latticeIsoperimetry`). As
`θ d = 1/(100 d) ≤ 1/12`, together with the planar statement it gives the Green-column input
`LatticeProb.External.SupercriticalBondGreenColumnExistence`
(`supercriticalBondGreenColumnExistence_of_latticeIsoperimetry`).
-/

open MeasureTheory Filter LatticeProb LatticeProb.Percolation Rigidity.External
  Rigidity.Proofs.S3
open scoped Classical

namespace Rigidity.Green

variable {d : ℕ}

/-- The scale bound `2⌈(2R)^θ⌉ + 1 ≤ 10 R^θ` for `R ≥ 1` and `0 ≤ θ ≤ 1`. -/
theorem two_mul_ceil_add_one_le {R : ℕ} (hR : 1 ≤ R) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    2 * (⌈(2 * (R : ℝ)) ^ θ⌉₊ : ℝ) + 1 ≤ 10 * (R : ℝ) ^ θ := by
  have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have ht1 : (1 : ℝ) ≤ (2 * (R : ℝ)) ^ θ := Real.one_le_rpow (by linarith) hθ0
  have hceil := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ (2 * (R : ℝ)) ^ θ)
  have hsplit : (2 * (R : ℝ)) ^ θ = (2 : ℝ) ^ θ * (R : ℝ) ^ θ :=
    Real.mul_rpow (by norm_num) (by linarith)
  have h2 : (2 : ℝ) ^ θ ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hθ1
  have hRθ : 0 ≤ (R : ℝ) ^ θ := Real.rpow_nonneg (by linarith) _
  have ht2 : (2 * (R : ℝ)) ^ θ ≤ 2 * (R : ℝ) ^ θ := by
    rw [hsplit]; exact mul_le_mul_of_nonneg_right h2 hRθ
  linarith

/-- **Cluster isoperimetry from well-connected cubes**: under the isoperimetric inequality of
`ℤ^d`, for `d ≥ 2` and `p_c(d) < p < 1`, almost surely the infinite cluster satisfies the
isoperimetric inequality in `y + Q_R` with constant `κ R^{-θd}`, `θ = 1/(10d)²`, for all large
`R` and all nonempty sets. -/
theorem clusterIsoperimetry_of_latticeIsoperimetry [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hLI : LatticeIsoperimetry d) :
    ClusterIsoperimetry d p 0 (1 / (10 * (d : ℝ)) ^ 2 * d) := by
  intro y
  filter_upwards [ae_eventually_isWellConnected hd hpc hp1
    Rigidity.Percolation.wellConnected_input y] with ω hω
  intro h _hy
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hω
  set C := uniqueInfiniteComponent h
  have hC : C.supp.Infinite := uniqueInfiniteComponent_infinite h
  set θ : ℝ := 1 / (10 * (d : ℝ)) ^ 2 with hθ
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ ≤ 1 := by
    rw [hθ, div_le_one (by positivity)]
    nlinarith
  refine ⟨1 / (4 * d * 10 ^ d), by positivity, max N₀ 30, fun R hR => ?_⟩
  have hR30 : 30 ≤ R := le_of_max_le_right hR
  have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast (by omega : 1 ≤ R)
  obtain ⟨hθN, -, hsub⟩ := hN₀ (2 * R) (by have := le_of_max_le_left hR; omega)
  push_cast at hθN hsub
  set t : ℝ := (2 * (R : ℝ)) ^ θ with ht
  set M : ℕ := ⌈t⌉₊ with hM
  have ht1 : (1 : ℝ) ≤ t := Real.one_le_rpow (by linarith) hθ0
  have hMt : t ≤ M := Nat.le_ceil t
  have hMlt : (M : ℝ) < t + 1 := Nat.ceil_lt_add_one (by linarith)
  have hM1 : 1 ≤ M := by
    have : (1 : ℝ) ≤ M := ht1.trans hMt
    exact_mod_cast this
  have hR30' : (30 : ℝ) ≤ R := by exact_mod_cast hR30
  have hMR : M + 1 ≤ R := by
    have : (M : ℝ) + 1 ≤ R := by linarith
    exact_mod_cast this
  have hgood : ∀ z ∈ cubeAt y (R + M + 1), IsGoodSubcube ω z M := by
    intro z hz
    refine hsub z M (by linarith) (by linarith) ⟨z, fun i => by simp, ?_⟩
    exact cubeAt_mono (by omega) hz
  have hiso := isoperimetricOn_of_isGoodSubcube C hC y (by omega : 1 ≤ d) hM1 hgood hLI
  rw [Real.rpow_zero]
  refine hiso.mono_const ?_
  have hRpos : (0 : ℝ) < R := by linarith
  have h2M := two_mul_ceil_add_one_le (by omega : 1 ≤ R) hθ0 hθ1
  have hpow : (2 * (M : ℝ) + 1) ^ d ≤ 10 ^ d * (R : ℝ) ^ (θ * d) := by
    rw [Real.rpow_mul hRpos.le, Real.rpow_natCast, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h2M d
  have hRτ : (R : ℝ) ^ (-(θ * d)) = ((R : ℝ) ^ (θ * d))⁻¹ := Real.rpow_neg hRpos.le _
  have hRτpos : 0 < (R : ℝ) ^ (θ * d) := Real.rpow_pos_of_pos hRpos _
  rw [hRτ]
  calc 1 / (4 * (d : ℝ) * 10 ^ d) * ((R : ℝ) ^ (θ * d))⁻¹
      = 1 / (4 * d * (10 ^ d * (R : ℝ) ^ (θ * d))) := by
        field_simp
    _ ≤ 1 / (4 * d * (2 * (M : ℝ) + 1) ^ d) := by
        apply one_div_le_one_div_of_le (by positivity)
        gcongr

/-- `θ d = 1/(100 d) ≤ 1/12` for `d ≥ 1`. -/
theorem coarseLoss_le {d : ℕ} (hd : 1 ≤ d) : 1 / (10 * (d : ℝ)) ^ 2 * d ≤ 1 / 12 := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hpos : (0 : ℝ) < (10 * (d : ℝ)) ^ 2 := by positivity
  rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ hpos (by norm_num)]
  nlinarith

/-- **The Green-column input** from the planar statement and the isoperimetric inequality of
`ℤ^d` in every dimension `d ≥ 3`. -/
theorem supercriticalBondGreenColumnExistence_of_latticeIsoperimetry
    (hTwo : Rigidity.External.SupercriticalBondGreenColumnExistenceTwo)
    (hLI : ∀ d : ℕ, 3 ≤ d → LatticeIsoperimetry d) :
    LatticeProb.External.SupercriticalBondGreenColumnExistence :=
  supercriticalBondGreenColumnExistence_of_isoperimetry hTwo fun d _ hd p hp hp1 =>
    ⟨0, 1 / (10 * (d : ℝ)) ^ 2 * d, le_rfl, by positivity,
      by rw [zero_add]; exact coarseLoss_le (by omega),
      clusterIsoperimetry_of_latticeIsoperimetry (by omega) hp hp1 (hLI d hd)⟩

end Rigidity.Green
