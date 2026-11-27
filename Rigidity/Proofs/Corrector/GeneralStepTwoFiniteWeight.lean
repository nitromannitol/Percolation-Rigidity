import Rigidity.Proofs.Corrector.GeneralStepTwoCapped

/-!
# The finite-range weight of the Step 2 sum on `ℤᵈ`: the cap scale and the good events

At scale `R` the cap is `n = ⌊log₃ R⌋` (`capScale`), so that `3ⁿ ≤ R`. The finite-range weight
dominates the weight of the Step 2 sum when no edge with its tail outside `B(u, R)` has `u` in its
box (`FarGood`) and the sides of the partition into good cubes are the sides of the partition capped
at scale `n` on `B(u, R)` (`SideGood`). The boxes are the `ℓ^∞` boxes `supBox`; `mem_supBox_trans`,
`supBox_subset_of_mem` and `cap_le_aux₁`, `cap_le_aux₂`, `cap_le_aux₃` are the radius bookkeeping
of the locality of the weight.

This ports the dimension-free part of the planar file `DarioStepTwoFiniteWeight`, with the side of
the partition into good cubes of `ℤᵈ` (`partSide`, `cappedSide`) in place of the planar sides.
-/

namespace Rigidity.Corrector.GeneralDim

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.Proofs.Cluster
  Rigidity.External
open Rigidity.Poincare.GeneralDim (supBox mem_supBox card_supBox)
open scoped Classical ENNReal

variable {d : ℕ}

/-- The cap scale `⌊log₃ R⌋`. -/
def capScale (R : ℕ) : ℕ := Nat.log 3 R

theorem three_pow_capScale_le {R : ℕ} (hR : 1 ≤ R) : 3 ^ capScale R ≤ R :=
  Nat.pow_log_le_self 3 (by omega)

theorem mem_supBox_trans {u v z : Vertex d} {r₁ r₂ : ℕ} (hz : z ∈ supBox v r₁)
    (hv : v ∈ supBox u r₂) : z ∈ supBox u (r₁ + r₂) := by
  rw [mem_supBox] at *
  intro i
  have t := abs_sub_le (z i) (v i) (u i)
  have := hz i
  have := hv i
  push_cast
  linarith

theorem supBox_subset_of_mem {u v : Vertex d} {r₁ r₂ : ℕ} (hv : v ∈ supBox u r₂) :
    (↑(supBox v r₁) : Set (Vertex d)) ⊆ ↑(supBox u (r₁ + r₂)) := fun _ hz =>
  Finset.mem_coe.2 (mem_supBox_trans (Finset.mem_coe.1 hz) hv)

theorem cap_le_aux₁ {κ R a : ℕ} (ha : a ≤ R) : 8 * a + R ≤ (3 * κ + 9) * R + 1 := by
  nlinarith

theorem cap_le_aux₂ {κ R a : ℕ} (ha : a ≤ R) :
    2 * R + 1 + (3 * κ * a + R) ≤ (3 * κ + 9) * R + 1 := by
  nlinarith

theorem cap_le_aux₃ {κ R c : ℕ} (hc : c ≤ R) : 3 * κ * c + R ≤ R + 3 * κ * R := by
  nlinarith

/-- No edge with its tail outside `B(u, R)` has `u` in its box. -/
def FarGood (κ R : ℕ) (ω : Configuration d) (u : Vertex d) : Prop :=
  ∀ v, u ∈ supBox v (3 * κ * partSide ω v) → v ∈ supBox u R

/-- The capped sides are the sides on `B(u, R)`. -/
def SideGood (R : ℕ) (ω : Configuration d) (u : Vertex d) : Prop :=
  ∀ v ∈ supBox u R, partSide ω v = cappedSide (capScale R) ω v

end Rigidity.Corrector.GeneralDim
