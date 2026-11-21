import Rigidity.Proofs.S2.DensityMomentGrowth
import Rigidity.Proofs.S2.RescaleExponentialMoment
import LatticeProb.Prob.StochasticO

/-!
# Density concentration from summable influence roots

Geometric tails on the grid `C n^κ` give a stretched-exponential tail with exponent `1/κ`. With
the moment growth of the triadic density this shows: if the moment roots of the single-bond
influences are summable with sum `C r^{2γ} (3^m + 1)^d`, then for every `0 < s ≤ 1/(γ + 1)`

`| |𝒞_∞ ∩ □| / |□| - θ(p) | ≤ 𝒪_s(C 3^{-dm/2})`

for every triadic cube `□` of size `3^m`.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory ProbabilityTheory LatticeProb.Percolation Rigidity.External
open scoped ENNReal

/-- Geometric tails on the grid `C n^κ` imply an `O_{1/κ}` tail bound. -/
theorem osBound_inv_of_geometric_tails {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (C : ℝ) (hC : 0 < C) (hX : ∀ ω, 0 ≤ X ω) (κ : ℕ)
    (hκ : 1 ≤ κ)
    (hgrid : ∀ n : ℕ, 1 ≤ n → μ {ω | C * (n : ℝ) ^ κ ≤ X ω} ≤ (1 / 2 : ℝ≥0∞) ^ n) :
    LatticeProb.OsBound μ (1 / (κ : ℝ)) (C * 4 ^ κ) X := by
  intro t ht
  let u : ℝ := t ^ (1 / (κ : ℝ))
  let n : ℕ := ⌊4 * u⌋₊
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hu1 : 1 ≤ u := Real.one_le_rpow ht (by positivity)
  have hu0 : 0 ≤ u := by linarith
  have hnUpper : (n : ℝ) ≤ 4 * u := Nat.floor_le (by positivity)
  have hnLower : 4 * u < (n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hn1 : 1 ≤ n := by
    have h1 : (1 : ℝ) ≤ n := by linarith
    exact_mod_cast h1
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have huPow : u ^ κ = t := by
    dsimp [u]
    simpa only [one_div] using Real.rpow_inv_natCast_pow ht0 (n := κ) (by omega)
  have hpow : (n : ℝ) ^ κ ≤ 4 ^ κ * t := by
    calc
      _ ≤ (4 * u) ^ κ := pow_le_pow_left₀ hn0 hnUpper _
      _ = 4 ^ κ * t := by rw [mul_pow, huPow]
  have hscale : C * (n : ℝ) ^ κ ≤ t * (C * 4 ^ κ) := by
    calc
      _ ≤ C * (4 ^ κ * t) := mul_le_mul_of_nonneg_left hpow hC.le
      _ = _ := by ring
  have hsub : {ω | t * (C * 4 ^ κ) < max (X ω) 0} ⊆ {ω | C * (n : ℝ) ^ κ ≤ X ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, max_eq_left (hX ω)] at hω
    exact hscale.trans hω.le
  have hlog : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h1 := Real.one_sub_inv_le_log_of_pos (x := (2 : ℝ)) (by norm_num)
    norm_num at h1 ⊢
    exact h1
  have harg : (n : ℝ) * (-Real.log 2) ≤ -u := by
    have h1 := mul_le_mul_of_nonneg_left hlog hn0
    nlinarith
  have hreal : (1 / 2 : ℝ) ^ n ≤ Real.exp (-u) := by
    calc
      _ = (Real.exp (-Real.log 2)) ^ n := by
        congr 1
        rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        norm_num
      _ = Real.exp ((n : ℝ) * (-Real.log 2)) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr harg
  have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  calc
    _ ≤ μ {ω | C * (n : ℝ) ^ κ ≤ X ω} := measure_mono hsub
    _ ≤ (1 / 2 : ℝ≥0∞) ^ n := hgrid n hn1
    _ = ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := by rw [ENNReal.ofReal_pow (by norm_num), hhalf]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

/-- The central-limit scale `3^{-dm/2}` is the inverse square root of the volume of a triadic
cube of size `3^m`. -/
theorem three_rpow_neg_half_mul (d m : ℕ) :
    (3 : ℝ) ^ (-((d : ℝ) * (m : ℝ)) / 2) = 1 / Real.sqrt ((((3 ^ m : ℕ) : ℝ)) ^ d) := by
  have hv : (((3 ^ m : ℕ) : ℝ)) ^ d = (3 : ℝ) ^ ((d : ℝ) * (m : ℝ)) := by
    rw [show (d : ℝ) * (m : ℝ) = ((m * d : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    push_cast
    rw [pow_mul]
  rw [hv, Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num), one_div,
    ← Real.rpow_neg (by norm_num)]
  congr 1
  ring

variable {d : ℕ} {p : unitInterval} {γ : ℕ}

/-- The centered density satisfies `|X| ≤ 𝒪_{1/(γ+1)}(C 3^{-dm/2})`. -/
theorem density_osBound (h : DensityInfluenceRootBound d p (2 * γ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (k : Vertex d),
      LatticeProb.OsBound
        (Measure.infinitePi (fun _ : Bond d => bernoulliMeasure (1 : ℝ) 0 p))
        (1 / ((γ + 1 : ℕ) : ℝ)) (C / Real.sqrt ((((3 ^ m : ℕ) : ℝ)) ^ d))
        (fun ω => |densityRealObservable p m k ω|) := by
  obtain ⟨C, hC, htail⟩ := density_moment_tail h
  refine ⟨C * 4 ^ (γ + 1), by positivity, fun m k => ?_⟩
  let P := Measure.infinitePi (fun _ : Bond d => bernoulliMeasure (1 : ℝ) 0 p)
  let w : ℝ := Real.sqrt ((((3 ^ m : ℕ) : ℝ)) ^ d)
  have hw : 0 < w := by dsimp [w]; positivity
  have hgrid (n : ℕ) (hn : 1 ≤ n) : P {ω | (C / w) * (n : ℝ) ^ (γ + 1) ≤
      |densityRealObservable p m k ω|} ≤ (1 / 2 : ℝ≥0∞) ^ n := by
    have heq : (C / w) * (n : ℝ) ^ (γ + 1) = C * (n : ℝ) ^ (γ + 1) / w := by ring
    simpa only [heq] using htail n hn m k
  have h1 := osBound_inv_of_geometric_tails P (fun ω => |densityRealObservable p m k ω|)
    (C / w) (by positivity) (fun ω => abs_nonneg _) (γ + 1) (by omega) hgrid
  have hscale : C / w * 4 ^ (γ + 1) = (C * 4 ^ (γ + 1)) / w := by ring
  simpa only [hscale] using h1

/-- A summable influence-root bound with exponent `2γ` gives the density concentration at every
exponent `0 < s ≤ 1/(γ + 1)` and the central-limit scale `3^{-dm/2}`. -/
theorem isOsBond_density_of_rootBound (h : DensityInfluenceRootBound d p (2 * γ)) (s : ℝ)
    (hs0 : 0 < s) (hs : s ≤ 1 / ((γ + 1 : ℕ) : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (k : Vertex d),
      IsOsBond d p
        (fun ω => |(infiniteClusterCount (triadicCube d m k) ω : ℝ) /
          ((triadicCube d m k).ncard : ℝ) - theta d p|) s
        (C * (3 : ℝ) ^ (-((d : ℝ) * (m : ℝ)) / 2)) := by
  obtain ⟨C, hC, htail⟩ := density_osBound h
  let L : ℝ := (16 : ℝ) ^ (1 / s)
  have hL : 0 < L := by positivity
  have hLs : L ^ s = 16 := by
    dsimp only [L]
    rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hs0.ne', Real.rpow_one]
  refine ⟨C * L, by positivity, fun m k => ?_⟩
  let P := Measure.infinitePi (fun _ : Bond d => bernoulliMeasure (1 : ℝ) 0 p)
  let X (ω : Bond d → ℝ) := |densityRealObservable p m k ω|
  let w : ℝ := Real.sqrt ((((3 ^ m : ℕ) : ℝ)) ^ d)
  let θ : ℝ := C / w
  have hw : 0 < w := by dsimp [w]; positivity
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hXm : Measurable X := (density_real_observable_properties p m k).1.abs
  have hsmall := integrable_scaled_exponential_of_osBound P X s θ hs0 hθ hXm
    ((htail m k).of_exponent_le hs)
  have hscale : C * L * (3 : ℝ) ^ (-((d : ℝ) * (m : ℝ)) / 2) = θ * L := by
    rw [three_rpow_neg_half_mul]
    dsimp only [θ, w]
    ring
  have hEq (ω : Bond d → ℝ) :
      (max (X ω / (θ * L)) 0) ^ s = (max (X ω) 0 / θ) ^ s / 16 := by
    have hX0 : 0 ≤ X ω := abs_nonneg _
    rw [max_eq_left (div_nonneg hX0 (by positivity)), max_eq_left hX0, div_mul_eq_div_div,
      Real.div_rpow (div_nonneg hX0 hθ.le) hL.le, hLs]
  rw [hscale]
  apply density_isOsBond_of_real_encoding p m k s (θ * L)
  change Integrable (fun ω => Real.exp ((max (X ω / (θ * L)) 0) ^ s)) P ∧
    (∫ ω, Real.exp ((max (X ω / (θ * L)) 0) ^ s) ∂P) ≤ 2
  simpa only [hEq] using hsmall

/-- A summable influence-root bound with exponent `2γ` gives the Dario–Gu density
concentration whenever `2(d-1)/(3d²+2d-1) ≤ 1/(γ + 1)`. -/
theorem clusterDensityConcentrationAt_of_rootBound (h : DensityInfluenceRootBound d p (2 * γ))
    (hs0 : 0 < 2 * ((d : ℝ) - 1) / (3 * (d : ℝ) ^ 2 + 2 * (d : ℝ) - 1))
    (hs : 2 * ((d : ℝ) - 1) / (3 * (d : ℝ) ^ 2 + 2 * (d : ℝ) - 1) ≤ 1 / ((γ + 1 : ℕ) : ℝ)) :
    ClusterDensityConcentrationAt d p :=
  isOsBond_density_of_rootBound h _ hs0 hs

end Rigidity.Proofs.S2
