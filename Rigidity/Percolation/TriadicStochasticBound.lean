import Rigidity.Percolation.TriadicSideLengthTail
import LatticeProb.Prob.StochasticO

/-!
# Stochastic bounds from triadic tails

A stretched-exponential tail at triadic thresholds yields a stochastic
stretched-exponential bound at arbitrary thresholds.
-/

namespace Rigidity.Percolation

open LatticeProb LatticeProb.Percolation MeasureTheory Filter
open scoped ENNReal

/-- A triadic stretched-exponential tail implies a stochastic bound with the
same exponent and a deterministic scale. -/
theorem osBound_of_triadic_tail (B c s : ℝ) (hB : 0 < B) (hc : 0 < c) (hs : 0 < s) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ),
      (∀ ω, 0 ≤ X ω) →
      (∀ n : ℕ, μ {ω | (3 : ℝ) ^ (n + 2) < X ω} ≤
        ENNReal.ofReal (B * Real.exp (-c * ((3 : ℝ) ^ n) ^ s))) →
      OsBound μ s θ X := by
  have hf := (tendsto_rpow_atTop hs).eventually
    (eventually_ge_atTop (((3 : ℝ) ^ s * (B + 1)) / c))
  obtain ⟨Q, hQ⟩ := eventually_atTop.1 hf
  let q := max Q 1
  have hq : 1 ≤ q := le_max_right _ _
  have hqp : ((3 : ℝ) ^ s * (B + 1)) / c ≤ q ^ s := hQ q (le_max_left _ _)
  refine ⟨9 * q, by positivity, ?_⟩
  intro Ω _ μ X hX htail t ht
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hq0 : 0 ≤ q := zero_le_one.trans hq
  have htq : 1 ≤ t * q := by nlinarith
  obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near htq (by norm_num : (1 : ℝ) < 3)
  have hp1 : 1 ≤ t ^ s := Real.one_le_rpow ht hs.le
  have hbase : (t * q) ^ s ≤ ((3 : ℝ) ^ (n + 1)) ^ s :=
    Real.rpow_le_rpow (mul_nonneg ht0 hq0) hn'.le hs.le
  have hqbound : (3 : ℝ) ^ s * (B + 1) ≤ c * q ^ s :=
    by simpa only [mul_comm] using (div_le_iff₀ hc).mp hqp
  have hpow : t ^ s * ((3 : ℝ) ^ s * (B + 1)) ≤
      c * ((3 : ℝ) ^ s * ((3 : ℝ) ^ n) ^ s) := by
    have h1 := mul_le_mul_of_nonneg_left hqbound (Real.rpow_nonneg ht0 s)
    have h2 := mul_le_mul_of_nonneg_left hbase hc.le
    rw [Real.mul_rpow ht0 hq0] at h2
    rw [pow_add, pow_one, Real.mul_rpow (by positivity) (by positivity)] at h2
    nlinarith
  have h3 : 0 < (3 : ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) _
  have hmain : t ^ s * (B + 1) ≤ c * ((3 : ℝ) ^ n) ^ s := by
    apply le_of_mul_le_mul_left _ h3
    nlinarith [hpow]
  have hexp : B ≤ Real.exp B := by linarith [Real.add_one_le_exp B]
  have he : -c * ((3 : ℝ) ^ n) ^ s ≤ -t ^ s - B := by nlinarith
  calc
    μ {ω | t * (9 * q) < max (X ω) 0} ≤ μ {ω | (3 : ℝ) ^ (n + 2) < X ω} := by
      apply measure_mono
      intro ω hω
      simp only [Set.mem_setOf_eq, max_eq_left (hX ω)] at hω
      change (3 : ℝ) ^ (n + 2) < X ω
      rw [pow_add]
      norm_num
      nlinarith
    _ ≤ ENNReal.ofReal (B * Real.exp (-c * ((3 : ℝ) ^ n) ^ s)) := htail n
    _ ≤ ENNReal.ofReal (Real.exp (-(t ^ s))) := by
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ B * Real.exp (-t ^ s - B) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hB.le
        _ = B / Real.exp B * Real.exp (-t ^ s) := by rw [Real.exp_sub, div_mul_eq_mul_div]; ring
        _ ≤ 1 * Real.exp (-t ^ s) := by
          gcongr
          exact (div_le_one (Real.exp_pos _)).2 hexp
        _ = _ := one_mul _

/-- Stopping-cube size bounds have a stochastic scale uniform in the vertex. -/
theorem TriadicCube.uniform_osBound_of_stopping_side {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (G : Ω → Set (TriadicCube d))
    (C : ℝ≥0∞) (hC : C ≠ ∞) (s c : ℝ) (hs : 0 < s) (hc : 0 < c)
    (hprob : ∀ R : TriadicCube d,
      μ {ω | R ∉ G ω} ≤ C * ENNReal.ofReal (Real.exp (-c * ((3 : ℝ) ^ R.scale) ^ s)))
    : ∃ θ : ℝ, 0 < θ ∧ ∀ (x : Vertex d) (X : Ω → ℝ),
      (∀ ω, 0 ≤ X ω) →
      (∀ ω, 0 < X ω → ∃ R : TriadicCube d,
        x ∈ R.vertices ∧ R.IsStopping (G ω) ∧ X ω ≤ (3 : ℝ) ^ R.scale) →
      OsBound μ s θ X := by
  let D : ℝ≥0∞ := (19 ^ d : ℝ≥0∞) * C *
    ∑' m : ℕ, ENNReal.ofReal (Real.exp (-c * ((3 : ℝ) ^ s - 1))) ^ m
  have hD : D ≠ ∞ := by
    apply ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) hC)
    exact stretched_exp_geometric_sum_ne_top ((3 : ℝ) ^ s) c
      (Real.one_lt_rpow (by norm_num) hs) hc
  let B : ℝ := max 1 D.toReal
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hDB : D ≤ ENNReal.ofReal B := by
    rw [← ENNReal.ofReal_toReal hD]
    exact ENNReal.ofReal_le_ofReal (le_max_right _ _)
  obtain ⟨θ, hθ, htail⟩ := osBound_of_triadic_tail B c s hB hc hs
  refine ⟨θ, hθ, ?_⟩
  intro x X hX hbound
  apply htail μ X hX
  intro n
  calc
    μ {ω | (3 : ℝ) ^ (n + 2) < X ω} ≤
        μ {ω | ∃ R : TriadicCube d, x ∈ R.vertices ∧ R.IsStopping (G ω) ∧
          n + 1 < R.scale} := by
      apply measure_mono
      intro ω hω
      change (3 : ℝ) ^ (n + 2) < X ω at hω
      have hp : 0 < (3 : ℝ) ^ (n + 2) := by positivity
      obtain ⟨R, hx, hR, hsize⟩ := hbound ω (hp.trans hω)
      refine ⟨R, hx, hR, ?_⟩
      by_contra h
      have hn : R.scale ≤ n + 1 := by omega
      have hpw : (3 : ℝ) ^ R.scale ≤ (3 : ℝ) ^ (n + 2) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
    _ ≤ (19 ^ d : ℝ≥0∞) * C * ENNReal.ofReal (Real.exp (-c * ((3 : ℝ) ^ n) ^ s)) *
        ∑' m : ℕ, ENNReal.ofReal (Real.exp (-c * ((3 : ℝ) ^ s - 1))) ^ m :=
      measure_exists_large_stopping_le_side_stretched μ G C s c hs hc hprob x n
    _ = D * ENNReal.ofReal (Real.exp (-c * ((3 : ℝ) ^ n) ^ s)) := by
      dsimp only [D]
      ac_rfl
    _ ≤ ENNReal.ofReal B * ENNReal.ofReal (Real.exp (-c * ((3 : ℝ) ^ n) ^ s)) :=
      mul_le_mul_left hDB _
    _ = ENNReal.ofReal (B * Real.exp (-c * ((3 : ℝ) ^ n) ^ s)) :=
      (ENNReal.ofReal_mul hB.le).symm

/-- A random variable bounded by the side length of a stopping cube at a fixed
point has a stretched-exponential stochastic bound. -/
theorem TriadicCube.osBound_of_stopping_side {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (G : Ω → Set (TriadicCube d))
    (C : ℝ≥0∞) (hC : C ≠ ∞) (s c : ℝ) (hs : 0 < s) (hc : 0 < c)
    (hprob : ∀ R : TriadicCube d,
      μ {ω | R ∉ G ω} ≤ C * ENNReal.ofReal (Real.exp (-c * ((3 : ℝ) ^ R.scale) ^ s)))
    (x : Vertex d) (X : Ω → ℝ) (hX : ∀ ω, 0 ≤ X ω)
    (hbound : ∀ ω, 0 < X ω → ∃ R : TriadicCube d,
      x ∈ R.vertices ∧ R.IsStopping (G ω) ∧ X ω ≤ (3 : ℝ) ^ R.scale) :
    ∃ θ : ℝ, 0 < θ ∧ OsBound μ s θ X := by
  obtain ⟨θ, hθ, h⟩ := uniform_osBound_of_stopping_side μ G C hC s c hs hc hprob
  exact ⟨θ, hθ, h x X hX hbound⟩

end Rigidity.Percolation
