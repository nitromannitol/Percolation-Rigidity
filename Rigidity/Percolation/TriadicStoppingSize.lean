import Rigidity.Percolation.TriadicStoppingMeasurable
import Rigidity.Percolation.TriadicStochasticMoment

/-!
# Measurable size of the stopping partition

The side length of the maximal stopping cube containing a fixed vertex is
measurable whenever the good-cube events are measurable.
-/

namespace Rigidity.Percolation

open LatticeProb LatticeProb.Percolation MeasureTheory
open scoped ENNReal

/-- The sum of the side lengths of maximal stopping cubes containing a vertex. -/
noncomputable def TriadicCube.stoppingSize {d : ℕ} (G : Set (TriadicCube d))
    (x : Vertex d) : ℝ := by
  classical
  exact (∑' Q : TriadicCube d, if x ∈ Q.vertices ∧ Q.IsMaximalStopping G then
    (3 : ℝ≥0∞) ^ Q.scale else 0).toReal

/-- A maximal stopping cube determines the size of the partition at its vertices. -/
theorem TriadicCube.stoppingSize_eq_of_mem {d : ℕ} {G : Set (TriadicCube d)}
    {x : Vertex d} {Q : TriadicCube d} (hx : x ∈ Q.vertices)
    (hQ : Q.IsMaximalStopping G) : stoppingSize G x = (3 : ℝ) ^ Q.scale := by
  classical
  unfold stoppingSize
  rw [tsum_eq_single Q]
  · simp only [hx, hQ, and_self, if_true, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
  · intro R hRQ
    rw [if_neg]
    rintro ⟨hxR, hR⟩
    exact hRQ (eq_of_isMaximalStopping_of_mem hR hQ hxR hx)

/-- The partition size vanishes at vertices outside every maximal stopping cube. -/
theorem TriadicCube.stoppingSize_eq_zero_of_not_exists {d : ℕ} {G : Set (TriadicCube d)}
    {x : Vertex d} (h : ¬ ∃ Q : TriadicCube d, x ∈ Q.vertices ∧ Q.IsMaximalStopping G) :
    stoppingSize G x = 0 := by
  classical
  unfold stoppingSize
  have heq : (∑' Q : TriadicCube d, if x ∈ Q.vertices ∧ Q.IsMaximalStopping G then
      (3 : ℝ≥0∞) ^ Q.scale else 0) = 0 := by
    apply ENNReal.tsum_eq_zero.mpr
    intro Q
    exact if_neg (fun hQ => h ⟨Q, hQ⟩)
  rw [heq, ENNReal.toReal_zero]

/-- The size of the stopping partition is nonnegative. -/
theorem TriadicCube.stoppingSize_nonneg {d : ℕ} (G : Set (TriadicCube d)) (x : Vertex d) :
    0 ≤ stoppingSize G x := ENNReal.toReal_nonneg

/-- The partition size is a measurable function of measurable good-cube events. -/
theorem TriadicCube.measurable_stoppingSize {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (G : Ω → Set (TriadicCube d))
    (hG : ∀ Q : TriadicCube d, MeasurableSet {ω | Q ∈ G ω}) (x : Vertex d) :
    Measurable (fun ω => stoppingSize (G ω) x) := by
  classical
  unfold stoppingSize
  apply ENNReal.measurable_toReal.comp
  apply Measurable.tsum
  intro Q
  by_cases hx : x ∈ Q.vertices
  · simpa only [hx, true_and] using
      (measurable_const.ite (measurableSet_isMaximalStopping G hG Q) measurable_const :
        Measurable (fun ω => if Q.IsMaximalStopping (G ω) then (3 : ℝ≥0∞) ^ Q.scale else 0))
  · simpa only [hx, false_and, if_false] using
      (measurable_const : Measurable (fun _ : Ω => (0 : ℝ≥0∞)))

/-- At every vertex of an existing maximal stopping cube, the partition size
is exactly that cube's side length. -/
theorem TriadicCube.exists_stopping_of_stoppingSize_pos {d : ℕ}
    (G : Set (TriadicCube d)) (x : Vertex d) (h : 0 < stoppingSize G x) :
    ∃ Q : TriadicCube d, x ∈ Q.vertices ∧ Q.IsStopping G ∧
      stoppingSize G x ≤ (3 : ℝ) ^ Q.scale := by
  classical
  by_contra hnot
  have hnone : ¬ ∃ Q : TriadicCube d, x ∈ Q.vertices ∧ Q.IsMaximalStopping G := by
    rintro ⟨Q, hx, hQ⟩
    apply hnot
    exact ⟨Q, hx, hQ.1, (stoppingSize_eq_of_mem hx hQ).le⟩
  rw [stoppingSize_eq_zero_of_not_exists hnone] at h
  exact (lt_irrefl 0) h

/-- Stretched-exponential good-cube probabilities give a finite exponential
moment for the size of the maximal stopping cube at a fixed vertex. -/
theorem TriadicCube.stoppingSize_exp_moment {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (G : Ω → Set (TriadicCube d))
    (hG : ∀ Q : TriadicCube d, MeasurableSet {ω | Q ∈ G ω})
    (C : ℝ≥0∞) (hC : C ≠ ∞) (s c : ℝ) (hs : 0 < s) (hc : 0 < c)
    (hprob : ∀ R : TriadicCube d,
      μ {ω | R ∉ G ω} ≤ C * ENNReal.ofReal (Real.exp (-c * ((3 : ℝ) ^ R.scale) ^ s)))
    (x : Vertex d) :
    ∃ θ : ℝ, 0 < θ ∧
      Integrable (fun ω => Real.exp ((stoppingSize (G ω) x / θ) ^ s)) μ ∧
      (∫ ω, Real.exp ((stoppingSize (G ω) x / θ) ^ s) ∂μ) ≤ 2 := by
  obtain ⟨θ, hθ, ht⟩ := osBound_of_stopping_side μ G C hC s c hs hc hprob x
    (fun ω => stoppingSize (G ω) x) (fun ω => stoppingSize_nonneg (G ω) x)
    (fun ω => exists_stopping_of_stoppingSize_pos (G ω) x)
  exact OsBound.exists_exp_rpow_integrable_le_two μ hs hθ
    (measurable_stoppingSize G hG x) (fun ω => stoppingSize_nonneg (G ω) x) ht

end Rigidity.Percolation
