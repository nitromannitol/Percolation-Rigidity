import Rigidity.Proofs.S2.ClusterDensityInfluenceBound
import Rigidity.Proofs.Percolation.PlanarFiniteCluster
import Rigidity.Proofs.Section5.ConnectingSet
import Mathlib.MeasureTheory.MeasurableSpace.NCard

/-!
# Finite-cluster size as a random variable

Finite component sizes are measurable and inherit stretched-exponential tails from planar
annulus crossings.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory LatticeProb.Percolation
open scoped ENNReal

variable {d : ℕ}

/-- The support of the component of a fixed vertex is a measurable random set. -/
theorem measurable_component_support (x : Vertex d) :
    Measurable fun ω : Configuration d => ((openGraph ω).connectedComponentMk x).supp := by
  apply measurable_set_iff.mpr
  intro y
  have heq : (fun ω : Configuration d => y ∈ ((openGraph ω).connectedComponentMk x).supp) =
      (fun ω => (openGraph ω).Reachable x y) := by
    funext ω
    apply propext
    constructor
    · intro hy
      exact (SimpleGraph.ConnectedComponent.exact
        ((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hy)).symm
    · intro hxy
      exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).2
        (SimpleGraph.ConnectedComponent.sound hxy.symm)
  rw [heq]
  exact measurableSet_setOf.1 (measurableSet_openGraph_reachable x y)

/-- The size of the finite component, taken to be zero for an infinite component, is measurable. -/
theorem measurable_finiteComponent_size (x : Vertex d) :
    Measurable fun ω : Configuration d => (finiteComponentVertices ω x).card := by
  have heq : (fun ω : Configuration d => (finiteComponentVertices ω x).card) =
      (fun ω => ((openGraph ω).connectedComponentMk x).supp.ncard) := by
    funext ω
    exact card_finiteComponentVertices ω x
  rw [heq]
  exact measurable_ncard.comp (measurable_component_support x)

/-- A supercritical planar finite-cluster size has a uniform exponential square-root moment. -/
theorem planar_finiteComponent_exp_sqrt_moment (p : unitInterval)
    (hp : criticalProbability 2 < (p : ℝ)) :
    ∃ a C : ℝ, 0 < a ∧ 0 < C ∧ ∀ x : Vertex 2,
      Integrable (fun ω => Real.exp (a * Real.sqrt ((finiteComponentVertices ω x).card : ℝ)))
          (latticeBondLaw 2 p) ∧
      (∫ ω, Real.exp (a * Real.sqrt ((finiteComponentVertices ω x).card : ℝ))
          ∂latticeBondLaw 2 p) ≤ C := by
  obtain ⟨C, c, hC, hc, htail⟩ := Rigidity.Percolation.planar_finite_cluster_size_tail_at p hp
  let b : ℕ → ℝ := fun n => (C + 1) * Real.exp (-(c / 2 * Real.sqrt n))
  have hb0 : ∀ n, 0 ≤ b n := fun n => by dsimp [b]; positivity
  have hbs : Summable b := by
    have h := (Rigidity.Proofs.S3.summable_exp_neg_mul_rpow (half_pos hc)
      (show (0 : ℝ) < 1 / 2 by norm_num)).mul_left (C + 1)
    simpa only [b, Real.sqrt_eq_rpow] using h
  let B := (∑' n, b n) + 1
  have hB : 0 < B := by dsimp [B]; linarith [show 0 ≤ ∑' n, b n from tsum_nonneg hb0]
  refine ⟨c / 2, B, by positivity, hB, fun x => ?_⟩
  let X : Configuration 2 → ℕ := fun ω => (finiteComponentVertices ω x).card
  let g : ℕ → ℝ := fun n => Real.exp (c / 2 * Real.sqrt n)
  have hXm : Measurable X := measurable_finiteComponent_size x
  have hmass : ∀ n : ℕ, latticeBondLaw 2 p {ω | X ω = n} ≤
      ENNReal.ofReal ((C + 1) * Real.exp (-(c * Real.sqrt n))) := by
    intro n
    by_cases hn : n = 0
    · subst n
      simp only [Nat.cast_zero, Real.sqrt_zero, mul_zero, neg_zero, Real.exp_zero, mul_one]
      calc
        _ ≤ (latticeBondLaw 2 p) Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
        _ ≤ ENNReal.ofReal (C + 1) := by rw [ENNReal.one_le_ofReal]; linarith
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      refine (measure_mono ?_).trans ((htail x n).trans (ENNReal.ofReal_le_ofReal ?_))
      · intro ω hω
        change X ω = n at hω
        have hsize : ((openGraph ω).connectedComponentMk x).supp.ncard = n := by
          simpa only [X, card_finiteComponentVertices] using hω
        have hf : ((openGraph ω).connectedComponentMk x).supp.Finite := by
          by_contra hnot
          have hz := (Set.not_finite.mp hnot).ncard
          omega
        exact ⟨hf, hsize.ge⟩
      · gcongr
        linarith
  have hterm : ∀ n, ENNReal.ofReal (g n) * latticeBondLaw 2 p {ω | X ω = n} ≤
      ENNReal.ofReal (b n) := by
    intro n
    refine (mul_le_mul_right (hmass n) _).trans ?_
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    apply ENNReal.ofReal_le_ofReal
    dsimp only [g, b]
    calc
      _ = (C + 1) * Real.exp (c / 2 * Real.sqrt n - c * Real.sqrt n) := by
        rw [sub_eq_add_neg, Real.exp_add]
        ring
      _ = (C + 1) * Real.exp (-(c / 2 * Real.sqrt n)) := by congr 1; congr 1; ring
      _ ≤ _ := le_rfl
  have hlin : ∫⁻ ω, ‖g (X ω)‖ₑ ∂latticeBondLaw 2 p ≤ ENNReal.ofReal B := by
    rw [← lintegral_map (f := fun n => ‖g n‖ₑ) measurable_from_nat hXm, lintegral_countable']
    calc
      _ = ∑' n, ENNReal.ofReal (g n) * latticeBondLaw 2 p {ω | X ω = n} := by
        congr 1
        ext n
        rw [Real.enorm_eq_ofReal (Real.exp_pos _).le,
          Measure.map_apply hXm (measurableSet_singleton n)]
        rfl
      _ ≤ ∑' n, ENNReal.ofReal (b n) := ENNReal.tsum_le_tsum hterm
      _ = ENNReal.ofReal (∑' n, b n) := (ENNReal.ofReal_tsum_of_nonneg hb0 hbs).symm
      _ ≤ ENNReal.ofReal B := ENNReal.ofReal_le_ofReal (by dsimp [B]; linarith)
  have hint : Integrable (fun ω => g (X ω)) (latticeBondLaw 2 p) :=
    ⟨((measurable_from_nat (f := g)).comp hXm).aestronglyMeasurable,
      hlin.trans_lt ENNReal.ofReal_lt_top⟩
  refine ⟨hint, ?_⟩
  have hreal : ENNReal.ofReal (∫ ω, g (X ω) ∂latticeBondLaw 2 p) ≤ ENNReal.ofReal B := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)]
    simpa only [g, Real.enorm_eq_ofReal (Real.exp_pos _).le] using hlin
  exact (ENNReal.ofReal_le_ofReal_iff hB.le).1 hreal

end Rigidity.Proofs.S2
