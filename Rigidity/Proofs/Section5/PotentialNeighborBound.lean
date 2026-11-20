import Rigidity.Proofs.Section5.ComponentHeatEquation
import LatticeProb.Network.FirstPassage

/-!
# Local bounds for truncated potential kernels

The potential kernel is nonnegative, and its value at a neighbor of its pole is at most one.
-/

open LatticeProb.Percolation LatticeProb.Graph LatticeProb.Network

namespace Rigidity.Proofs.Section5

/-- A truncated potential is the normalized difference of two expected local times. -/
theorem truncatedComponentPotential_eq_localTime {d : ℕ} {ω : Configuration d}
    (C : OpenComponent ω) (n : ℕ) (y x : C) :
    truncatedComponentPotential C n y x =
      (meanLocalTime (componentGraph C) n y y - meanLocalTime (componentGraph C) n x y) /
        (componentGraph C).degree y := by
  simp only [truncatedComponentPotential, meanLocalTime, ← Finset.sum_sub_distrib, ← Finset.sum_div]

/-- The truncated potential kernel is nonnegative. -/
theorem truncatedComponentPotential_nonneg {d : ℕ} {ω : Configuration d}
    (C : OpenComponent ω) (n : ℕ) (y x : C) :
    0 ≤ truncatedComponentPotential C n y x := by
  rw [truncatedComponentPotential_eq_localTime]
  exact div_nonneg (sub_nonneg.mpr (meanLocalTime_le_self n x y)) (Nat.cast_nonneg _)

/-- At a neighbor of the pole, the truncated potential is bounded uniformly by one. -/
theorem truncatedComponentPotential_le_one_of_adj {d : ℕ} {ω : Configuration d}
    (C : OpenComponent ω) (n : ℕ) (y x : C) (hxy : (componentGraph C).Adj y x) :
    truncatedComponentPotential C n y x ≤ 1 := by
  classical
  let G := componentGraph C
  have hd : (0 : ℝ) < G.degree y := by
    have : 0 < G.degree y := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      exact Finset.card_pos.mpr ⟨x, (G.mem_neighborFinset y x).mpr hxy⟩
    exact_mod_cast this
  have hsum : ∑ z ∈ G.neighborFinset y,
      (meanLocalTime G n y y - meanLocalTime G n z y) ≤ G.degree y := by
    have hstep := meanLocalTime_succ (G := G) n y y
    have hmono := meanLocalTime_mono (G := G) n y y
    simp only [if_true, walkOp] at hstep
    rw [Finset.sum_sub_distrib, Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree,
      nsmul_eq_mul]
    have hstep' : (G.degree y : ℝ) * meanLocalTime G (n + 1) y y =
        (G.degree y : ℝ) + ∑ z ∈ G.neighborFinset y, meanLocalTime G n z y := by
      field_simp at hstep
      linarith
    nlinarith
  have hterm : meanLocalTime G n y y - meanLocalTime G n x y ≤
      ∑ z ∈ G.neighborFinset y,
        (meanLocalTime G n y y - meanLocalTime G n z y) :=
    Finset.single_le_sum (fun z _ => sub_nonneg.mpr (meanLocalTime_le_self n z y))
      ((G.mem_neighborFinset y x).mpr hxy)
  rw [truncatedComponentPotential_eq_localTime, div_le_one hd]
  exact hterm.trans hsum

end Rigidity.Proofs.Section5
