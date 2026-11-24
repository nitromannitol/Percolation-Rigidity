import PercolationClusterHomogenization.Proofs.Density.ResamplingExchangeable
import LatticeProb.Prob.EfronSteinCountable

/-!
# Symmetry of weighted resampling differences

The two endpoint weights give the same integral against a squared one-coordinate resampling
difference.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory ProbabilityTheory LatticeProb

/-- Exchanging the endpoints of a resampling difference preserves its weighted integral. -/
theorem integral_resampling_endpoint_symmetry {ι : Type*} [DecidableEq ι]
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (F : (ι → ℝ) → ℝ) (hF : Measurable F)
    (i : ι) (n : ℕ) :
    let P := Measure.infinitePi (fun _ : ι => ν)
    (∫ q : (ι → ℝ) × (ι → ℝ), |F q.1| ^ n *
      (F q.1 - F (Function.update q.1 i (q.2 i))) ^ 2 ∂(P.prod P)) =
    ∫ q : (ι → ℝ) × (ι → ℝ), |F (Function.update q.1 i (q.2 i))| ^ n *
      (F q.1 - F (Function.update q.1 i (q.2 i))) ^ 2 ∂(P.prod P) := by
  classical
  let P := Measure.infinitePi (fun _ : ι => ν)
  let S (q : (ι → ℝ) × (ι → ℝ)) :=
    (Function.update q.1 i (q.2 i), Function.update q.2 i (q.1 i))
  let G (q : (ι → ℝ) × (ι → ℝ)) := |F q.1| ^ n *
    (F q.1 - F (Function.update q.1 i (q.2 i))) ^ 2
  have hS : MeasurePreserving S (P.prod P) (P.prod P) := measurePreserving_swap_coordinate ν i
  have hG : Measurable G := by
    dsimp only [G]
    have hu : Measurable (fun q : (ι → ℝ) × (ι → ℝ) =>
        Function.update q.1 i (q.2 i)) :=
      (measurable_updateAt i).comp (measurable_fst.prodMk (measurable_pi_apply i |>.comp measurable_snd))
    exact ((hF.comp measurable_fst).abs.pow_const n).mul
      (((hF.comp measurable_fst).sub (hF.comp hu)).pow_const 2)
  have hmap : (∫ q, G q ∂(P.prod P)) = ∫ q, G (S q) ∂(P.prod P) := by
    have hm : AEStronglyMeasurable G (Measure.map S (P.prod P)) := by
      rw [hS.map_eq]
      exact hG.aestronglyMeasurable
    have h := integral_map hS.measurable.aemeasurable hm
    rwa [hS.map_eq] at h
  change (∫ q, G q ∂(P.prod P)) =
    ∫ q : (ι → ℝ) × (ι → ℝ), |F (Function.update q.1 i (q.2 i))| ^ n *
      (F q.1 - F (Function.update q.1 i (q.2 i))) ^ 2 ∂(P.prod P)
  rw [hmap]
  apply integral_congr_ae
  filter_upwards with q
  have hupdate : Function.update (Function.update q.1 i (q.2 i)) i
      ((Function.update q.2 i (q.1 i)) i) = q.1 := by
    simp
  dsimp only [G, S]
  rw [hupdate]
  ring

end Rigidity.Proofs.S2
