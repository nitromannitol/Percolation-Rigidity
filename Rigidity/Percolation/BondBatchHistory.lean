import Rigidity.Percolation.BondRevealHistory

/-!
# Fully open seed tests

A seed test reads all internal bonds of a finite region. Adaptive exploration
of fresh seeds inherits a geometric survival bound.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory

/-- The test for all internal bonds of a finite region being open. -/
noncomputable def fullyOpenRegionTest {d : ℕ} (U : Set (Vertex d)) (hU : U.Finite) :
    BondTest d := by
  classical
  exact { bonds := localBonds U
          finite_bonds := finite_localBonds hU
          outcome := fun ω => if ω ∈ fullyOpenRegion U then true else false
          measurable_outcome := measurable_const.piecewise
            (measurableSet_fullyOpenRegion_localBond U) measurable_const }

/-- A seed test succeeds exactly when all its bonds are open. -/
theorem fullyOpenRegionTest_outcome {d : ℕ} (U : Set (Vertex d)) (hU : U.Finite)
    (ω : Configuration d) :
    (fullyOpenRegionTest U hU).outcome ω = true ↔ ω ∈ fullyOpenRegion U := by
  classical
  simp [fullyOpenRegionTest]

/-- Adaptive tests of fresh bounded seeds have geometric survival probability.
The exploration can choose each seed after observing the full base field and
all preceding seed outcomes. -/
theorem measureReal_prod_survival_le_of_seed_tests {d : ℕ}
    (q r : unitInterval) (N : ℕ)
    (U : Configuration d → List Bool → Set (Vertex d))
    (hU : ∀ b h, (U b h).Finite)
    (hN : ∀ b h, (finite_localBonds (hU b h)).toFinset.card ≤ N)
    (hfresh : ∀ b h, Disjoint (localBonds (U b h))
      (historyBonds (fun g => fullyOpenRegionTest (U b g) (hU b g)) h))
    (S : Configuration d → ℕ → Set (List Bool))
    (G : ℕ → Set (Configuration d × Configuration d))
    (hsection : ∀ b n ω, (b, ω) ∈ G n ↔
      observedBondHistory (fun h => fullyOpenRegionTest (U b h) (hU b h)) ω n ∈ S b n)
    (hG : ∀ n, MeasurableSet (G n)) (hdecr : ∀ n, G (n + 1) ⊆ G n)
    (hstop : ∀ b h, h ++ [true] ∉ S b (h.length + 1)) :
    ∀ n, ((latticeBondLaw d q).prod (latticeBondLaw d r)).real (G n) ≤
      (1 - (r : ℝ) ^ N) ^ n := by
  let next := fun b h => fullyOpenRegionTest (U b h) (hU b h)
  apply measureReal_prod_survival_le_of_bond_revelation q r N next
    (fun b _ h => U b h.1) (fun b _ h => hU b h.1) (fun b _ h => hN b h.1)
    (fun b _ h => hfresh b h.1) S G hsection hG hdecr
  intro b n h
  apply Set.disjoint_left.mpr
  intro ω hsurv hseed
  have hh := observedBondHistory_eq_of_mem (next b) ω h.1 hsurv.2
  rw [h.2] at hh
  have htrue : (next b h.1).outcome ω = true :=
    (fullyOpenRegionTest_outcome (U b h.1) (hU b h.1) ω).mpr hseed
  have hs := (hsection b (n + 1) ω).mp hsurv.1
  change (observedBondHistory (next b) ω (n + 1)) ∈ S b (n + 1) at hs
  rw [observedBondHistory, hh, htrue] at hs
  have hstop' : h.1 ++ [true] ∉ S b (n + 1) := by
    simpa only [h.2] using hstop b h.1
  exact hstop' hs

end Rigidity.Percolation
