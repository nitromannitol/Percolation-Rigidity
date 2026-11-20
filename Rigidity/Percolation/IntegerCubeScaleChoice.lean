import Mathlib.Tactic

/-!
# Compatible scales for overlapping lattice cubes

Two odd box sizes derived from radii divisible by four fit inside a sufficiently
large ambient cube and provide the overlap and path thresholds needed for a
subcube cover.
-/

namespace Rigidity.Percolation

/-- Two radii with a common parameter give compatible enlarged-box sizes and
a path threshold proportional to the ambient side. -/
theorem exists_compatible_subcube_scales (S : ℕ) (hS : 61 ≤ S) :
    ∃ t : ℕ, 3 ≤ t ∧
      let s := 20 * t + 1
      let k := 10 * t + 1
      let R := 2 * t
      s = 2 * ((5 * (8 * t)) / 4) + 1 ∧
      k = 2 * ((5 * (4 * t)) / 4) + 1 ∧
      2 * R + 1 ≤ s ∧ k + 1 ≤ s ∧ R + 1 ≤ k ∧ s ≤ S ∧
      10 * R ≤ S ∧ S ≤ 20 * t + 20 := by
  refine ⟨(S - 1) / 20, ?_⟩
  have hdiv := Nat.div_add_mod (S - 1) 20
  have hmod := Nat.mod_lt (S - 1) (by omega : 0 < 20)
  dsimp only
  omega

end Rigidity.Percolation
