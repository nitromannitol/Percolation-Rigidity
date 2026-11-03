import Rigidity.Steps.S4.EffectiveResistanceRecurrence
import LatticeProb.Network.OpenLadderKirchhoff
import LatticeProb.Network.OpenLadderConnected
import LatticeProb.Network.Dirichlet

/-!
# The unit voltage of the gadget network

The unit voltage of `Section4.IsUnitVoltage` is the solution of the Dirichlet problem on the
finite connected gadget network with boundary values zero at the source and one at the target:
it exists and is unique (`step:4.2-unique-voltage`). At height one, Kirchhoff's equations at the
two rung vertices give the unit current `h(a) = 1/3`, hence the effective resistance `R_1 = 3`
(paper L1170-1175).
-/

namespace Rigidity.Proofs.S4

open LatticeProb.Network LatticeProb.Network.OpenLadder Rigidity.Section4

/-- The sum in `IsUnitVoltage` is the unit-conductance network Laplacian. -/
theorem sum_adj_sub_eq_netLaplacian {n : ℤ} (h : Vertex n → ℝ) (v : Vertex n) :
    (∑ w : Vertex n, if (graph n).Adj v w then h w - h v else 0) =
      netLaplacian (graph n) (unitCond (graph n)) h v := by
  rw [netLaplacian_unitCond, LatticeProb.Graph.laplacian, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext w
  simp

/-- A unit voltage is a function harmonic off the two terminals, with value zero at the source
and one at the target. -/
theorem isUnitVoltage_iff {n : ℤ} (h : Vertex n → ℝ) :
    IsUnitVoltage n h ↔ h (source n) = 0 ∧ h (target n) = 1 ∧ Harmonic h := by
  simp only [IsUnitVoltage, Harmonic, HarmonicOn, sum_adj_sub_eq_netLaplacian,
    Set.mem_setOf_eq, and_imp]

/-- The two terminals of the gadget network are distinct. -/
theorem source_ne_target (n : ℤ) : source n ≠ target n := by
  simp [source, target]

/-- The unit voltage of the gadget network of height `n ≥ 1` exists and is unique. -/
theorem existsUnique_isUnitVoltage {n : ℤ} (hn : 1 ≤ n) :
    ∃! h : Vertex n → ℝ, IsUnitVoltage n h := by
  classical
  let A : Finset (Vertex n) := Finset.univ.filter fun v => v ≠ source n ∧ v ≠ target n
  let g : Vertex n → ℝ := fun v => if v = target n then 1 else 0
  have hacc : BoundaryAccessible (graph n) A :=
    boundaryAccessible_of_connected (connected hn) A ⟨source n, by simp [A]⟩
  have key : ∀ u, SolvesDirichlet (graph n) (unitCond (graph n)) A g u ↔ IsUnitVoltage n u := by
    intro u
    rw [isUnitVoltage_iff, SolvesDirichlet]
    constructor
    · rintro ⟨hharm, hbd⟩
      refine ⟨?_, ?_, fun v hv => hharm v (by simpa [A] using hv)⟩
      · rw [hbd (source n) (by simp [A])]
        simp [g, source_ne_target n]
      · rw [hbd (target n) (by simp [A])]
        simp [g]
    · rintro ⟨hs, ht, hharm⟩
      refine ⟨fun v hv => hharm v (by simpa [A] using hv), fun v hv => ?_⟩
      have hv' : v = source n ∨ v = target n := by
        by_contra hc
        exact hv (by simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]; tauto)
      rcases hv' with rfl | rfl
      · simp [g, hs, source_ne_target n]
      · simp [g, ht]
  obtain ⟨f, hf, huniq⟩ := existsUnique_dirichlet isCond_unitCond A hacc g
  exact ⟨f, (key f).1 hf, fun u hu => huniq u ((key u).2 hu)⟩

/-- Step `step:4.2-unique-voltage`. -/
theorem unitVoltageExistsUnique : Steps.S4.UnitVoltageExistsUniqueStep :=
  fun n hn => existsUnique_isUnitVoltage (by exact_mod_cast hn)

/-- Kirchhoff's equations at the two rung vertices of the gadget of height one give the unit
current `h(a) = 1/3`. -/
theorem unitVoltage_one_left {h : Vertex 1 → ℝ} (hs : h (source 1) = 0)
    (ht : h (target 1) = 1) (hharm : Harmonic h) :
    h (left 1 1 ⟨le_rfl, le_rfl⟩) = 1 / 3 := by
  have h1 := kirchhoff_left_one hharm
  have h2 := kirchhoff_right_one hharm
  rw [hs] at h1
  rw [ht] at h2
  linarith

/-- Step `step:4.2-current` at height one: `R_1 = 3`. -/
theorem resistanceBase : Steps.S4.ResistanceBaseStep := by
  intro h hh
  obtain ⟨hs, ht, hharm⟩ := (isUnitVoltage_iff h).1 hh
  have ha : h (siteA 1 le_rfl) = 1 / 3 := unitVoltage_one_left (h := h) hs ht hharm
  rw [ha]
  norm_num

end Rigidity.Proofs.S4
