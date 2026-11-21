import Rigidity.Proofs.Percolation.PlanarFiniteVolumeInverseLimit
import Rigidity.Proofs.Percolation.PlanarOmegaStepOne

/-!
# The limit of `D_n`

From the scale of uniform ellipticity on, `D_n = ∑ᵢ (E[ν(□_n, eᵢ)] - (1/2) eᵢ · ā_{□_n} eᵢ)`, since
`E[-μ(□_n, ā_{□_n} r)] = (1/2) r · ā_{□_n} r`. Hence `D_n` converges to
`(1/2) ∑ᵢ (ā_{ii} - (L⁻¹)_{ii})`, where `L` is the limit of the matrices `ā_{□_n}⁻¹`.
-/

open MeasureTheory Filter Topology LatticeProb.Percolation Rigidity.External
  Rigidity.Proofs.Section5
open scoped Classical Matrix

namespace Rigidity.Percolation

theorem mulVec_single_apply_self (A : Matrix (Fin 2) (Fin 2) ℝ) (i : Fin 2) :
    (A *ᵥ Pi.single i 1) i = A i i := by
  simp [Matrix.mulVec]

/-- `lim E[ν(□_n, eᵢ)] = (1/2) ā_{ii}`. -/
theorem planarNuLimit_single {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (i : Fin 2) : planarNuLimit p (Pi.single i 1) = 1 / 2 * planarAhom p i i := by
  rw [planarNuLimit_eq_planarAhom hpc]
  fin_cases i <;> simp [Fin.sum_univ_two]

/-- **The limit of `D_n`.** -/
theorem tendsto_planarOmegaD {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) :
    Tendsto (planarOmegaD p) atTop
      (𝓝 (1 / 2 * ∑ i : Fin 2, (planarAhom p i i - (planarAhomInvLimit p)⁻¹ i i))) := by
  obtain ⟨C, -, N, hN⟩ := exists_planarAhomInvFinite_mulVec_planarAhomFinite hpc
  have heq : ∀ n, N ≤ n → planarOmegaD p n =
      ∑ i : Fin 2, (planarNuMean p n (Pi.single i 1) - 1 / 2 * planarAhomFinite p n i i) := by
    intro n hn
    obtain ⟨hinv, -, -⟩ := hN n hn
    rw [planarOmegaD]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [planarMuMean_planarAhomFinite hpc hinv, sum_single_mul, mulVec_single_apply_self]
    ring
  have hlim : Tendsto (fun n => ∑ i : Fin 2,
      (planarNuMean p n (Pi.single i 1) - 1 / 2 * planarAhomFinite p n i i)) atTop
      (𝓝 (∑ i : Fin 2, (1 / 2 * planarAhom p i i - 1 / 2 * (planarAhomInvLimit p)⁻¹ i i))) := by
    refine tendsto_finsetSum _ fun i _ => ?_
    rw [← planarNuLimit_single hpc i]
    exact (tendsto_planarNuLimit hpc _).sub ((tendsto_planarAhomFinite hpc i i).const_mul _)
  have e : ∑ i : Fin 2, (1 / 2 * planarAhom p i i - 1 / 2 * (planarAhomInvLimit p)⁻¹ i i) =
      1 / 2 * ∑ i : Fin 2, (planarAhom p i i - (planarAhomInvLimit p)⁻¹ i i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [← e]
  exact hlim.congr' (eventually_atTop.2 ⟨N, fun n hn => (heq n hn).symm⟩)

end Rigidity.Percolation
