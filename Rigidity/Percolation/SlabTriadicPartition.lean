import Rigidity.Percolation.SlabTriadicOverlap
import Rigidity.Percolation.TriadicLargeScaleDecay

/-!
# Triadic partitions from slab connectivity

Uniform two-point connectivity in complete slabs yields the stopping partition,
its size moment, and its localization bound through the well-connected-cube
construction.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory Rigidity.External
open scoped ENNReal

/-- Uniform full-slab two-point connectivity implies the triadic stopping
partition, exponential size moment, and localization estimate for the rounded
three-quarter interior. -/
theorem triadic_partition_estimates_of_twoPoint_slabs {d : ℕ}
    (hd : 0 < d) (j i : Fin d) (hij : i ≠ j) (width : ℕ) (hwidth : 0 < width)
    (p : unitInterval) (ρ c : ℝ) (hρ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) (hc : 0 < c)
    (hcρ : c ≤ ρ) (hcroot : c ≤ (p : ℝ) * ρ ^ (2 * d))
    (hctwo : c ≤ (p : ℝ) * ((p : ℝ) * ρ))
    (hslab : ∀ U : IntegerCube d, ∀ a : Fin d, ∀ k : ℕ, (k + 1) * width ≤ U.size →
      ∀ x ∈ U.slab a width k, ∀ y ∈ U.slab a width k,
        ρ ≤ (latticeBondLaw d p).real {ω | (openIn ω (U.slab a width k)).Reachable x y}) :
    let G : Configuration d → Set (TriadicCube d) := fun ω =>
      TriadicCube.goodOfWellConnected (TriadicCube.wellConnectedFamily
        (fun Q => Q.threeQuarterCube.vertices) ω)
    (∀ᵐ ω ∂(latticeBondLaw d p), ∀ x : Vertex d,
      ∃! Q : TriadicCube d, x ∈ Q.vertices ∧ Q.IsMaximalStopping (G ω)) ∧
    (∃ θ : ℝ, 0 < θ ∧ ∀ x : Vertex d,
      Integrable (fun ω => Real.exp (TriadicCube.stoppingSize (G ω) x / θ)) (latticeBondLaw d p) ∧
      (∫ ω, Real.exp (TriadicCube.stoppingSize (G ω) x / θ) ∂(latticeBondLaw d p)) ≤ 2) ∧
    (∃ K k : ℝ, 0 < K ∧ 0 < k ∧ ∀ (A : TriadicCube d) (n : ℕ),
      (latticeBondLaw d p) {ω | ∃ x ∈ A.boundaryInterior n, ∃ Q R : TriadicCube d,
        x ∈ Q.vertices ∧ x ∈ R.vertices ∧ Q.IsMaximalStopping (G ω) ∧
          R.IsMaximalStopping (TriadicCube.localGoodCentered (G ω) A.vertices) ∧ Q ≠ R} ≤
        ENNReal.ofReal (K * (3 : ℝ) ^ ((A.scale : ℝ) - n) *
          Real.exp (-k * (3 : ℝ) ^ n))) := by
  obtain ⟨M, hM⟩ :=
    TriadicCube.eventually_measure_not_wellConnectedIn_threeQuarter_le_of_twoPoint_slabs
      hd j i hij width hwidth p ρ c hρ hρ₁ hc hcρ hcroot hctwo hslab
  let rate : ℝ := ((c / (2 * ((10 * d * width : ℕ) : ℝ))) / 2) / 40
  let C : ℝ := 1 + 4 * 7 ^ d * ((d + 1).factorial : ℝ) / (rate / 2) ^ (d + 1)
  have hrate : 0 < rate := by dsimp only [rate]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hlarge : ∀ Q : TriadicCube d, M ≤ Q.scale →
      (latticeBondLaw d p) {ω | ¬ Q.wellConnectedIn Q.threeQuarterCube.vertices ω} ≤
        ENNReal.ofReal (C * Real.exp (-(rate / 2) * (3 : ℝ) ^ Q.scale)) := by
    intro Q hscale
    have hpow : M ≤ 3 ^ Q.scale := by
      calc
        M ≤ 2 ^ M := Nat.le_of_lt Nat.lt_two_pow_self
        _ ≤ 3 ^ M := by gcongr; omega
        _ ≤ 3 ^ Q.scale := pow_le_pow_right₀ (by omega) hscale
    exact hM Q hpow
  exact TriadicCube.partition_estimates_of_large_scale hd (latticeBondLaw d p)
    (fun Q => Q.threeQuarterCube.vertices) M C (rate / 2) hC (by positivity) hlarge

/-- A single finite width has a uniform positive two-point connection bound
in every complete slab of every integer cube. For `d = 2`, such a bound
requires `p = 1` because a fixed-width strip has arbitrarily many disjoint cuts. -/
def UniformCubeSlabConnectivity (d : ℕ) (p : unitInterval) : Prop :=
  ∃ width : ℕ, 0 < width ∧ ∃ ρ : ℝ, 0 < ρ ∧
    ∀ U : IntegerCube d, ∀ a : Fin d, ∀ k : ℕ, (k + 1) * width ≤ U.size →
      ∀ x ∈ U.slab a width k, ∀ y ∈ U.slab a width k,
        ρ ≤ (latticeBondLaw d p).real {ω | (openIn ω (U.slab a width k)).Reachable x y}

/-- The lower probability bound in uniform slab connectivity can be chosen
at most one, and positive bond density supplies a positive common decay rate. -/
theorem UniformCubeSlabConnectivity.exists_parameters {d : ℕ} {p : unitInterval}
    (j : Fin d) (hp : 0 < (p : ℝ)) (h : UniformCubeSlabConnectivity d p) :
    ∃ width : ℕ, 0 < width ∧ ∃ ρ c : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ 0 < c ∧
      c ≤ ρ ∧ c ≤ (p : ℝ) * ρ ^ (2 * d) ∧ c ≤ (p : ℝ) * ((p : ℝ) * ρ) ∧
      ∀ U : IntegerCube d, ∀ a : Fin d, ∀ k : ℕ, (k + 1) * width ≤ U.size →
        ∀ x ∈ U.slab a width k, ∀ y ∈ U.slab a width k,
          ρ ≤ (latticeBondLaw d p).real {ω | (openIn ω (U.slab a width k)).Reachable x y} := by
  obtain ⟨width, hwidth, ρ, hρ, hslab⟩ := h
  let U : IntegerCube d := ⟨0, width⟩
  have hx : (0 : Vertex d) ∈ U.slab j width 0 := by
    have hwidth' : (0 : ℤ) < width := by exact_mod_cast hwidth
    refine ⟨?_, ?_, ?_⟩
    · rw [U.mem_vertices]
      intro a
      simpa only [U, Pi.zero_apply, zero_add] using And.intro (le_refl (0 : ℤ)) hwidth'
    · simp [U]
    · simpa [U] using hwidth'
  have hρ₁ : ρ ≤ 1 := by
    exact (hslab U j 0 (by simp only [U, zero_add, one_mul, le_refl]) 0 hx 0 hx).trans
      (measureReal_le_one (μ := latticeBondLaw d p) (s :=
        {ω | (openIn ω (U.slab j width 0)).Reachable 0 0}))
  obtain ⟨c, hc, hcρ, hcroot, hctwo⟩ := exists_slab_decay_rate p ρ hp hρ
  exact ⟨width, hwidth, ρ, c, hρ, hρ₁, hc, hcρ, hcroot, hctwo, hslab⟩

/-- Uniform positive slab connectivity gives the partition and its quantitative
estimates whenever the bond density is positive. -/
theorem triadic_partition_estimates_of_uniformCubeSlabConnectivity {d : ℕ}
    (hd : 0 < d) (j i : Fin d) (hij : i ≠ j) (p : unitInterval) (hp : 0 < (p : ℝ))
    (hslab : UniformCubeSlabConnectivity d p) :
    let G : Configuration d → Set (TriadicCube d) := fun ω =>
      TriadicCube.goodOfWellConnected (TriadicCube.wellConnectedFamily
        (fun Q => Q.threeQuarterCube.vertices) ω)
    (∀ᵐ ω ∂(latticeBondLaw d p), ∀ x : Vertex d,
      ∃! Q : TriadicCube d, x ∈ Q.vertices ∧ Q.IsMaximalStopping (G ω)) ∧
    (∃ θ : ℝ, 0 < θ ∧ ∀ x : Vertex d,
      Integrable (fun ω => Real.exp (TriadicCube.stoppingSize (G ω) x / θ)) (latticeBondLaw d p) ∧
      (∫ ω, Real.exp (TriadicCube.stoppingSize (G ω) x / θ) ∂(latticeBondLaw d p)) ≤ 2) ∧
    (∃ K k : ℝ, 0 < K ∧ 0 < k ∧ ∀ (A : TriadicCube d) (n : ℕ),
      (latticeBondLaw d p) {ω | ∃ x ∈ A.boundaryInterior n, ∃ Q R : TriadicCube d,
        x ∈ Q.vertices ∧ x ∈ R.vertices ∧ Q.IsMaximalStopping (G ω) ∧
          R.IsMaximalStopping (TriadicCube.localGoodCentered (G ω) A.vertices) ∧ Q ≠ R} ≤
        ENNReal.ofReal (K * (3 : ℝ) ^ ((A.scale : ℝ) - n) *
          Real.exp (-k * (3 : ℝ) ^ n))) := by
  obtain ⟨width, hwidth, ρ, c, hρ, hρ₁, hc, hcρ, hcroot, hctwo, hprob⟩ :=
    hslab.exists_parameters j hp
  exact triadic_partition_estimates_of_twoPoint_slabs hd j i hij width hwidth p ρ c
    hρ.le hρ₁ hc hcρ hcroot hctwo hprob

end Rigidity.Percolation
