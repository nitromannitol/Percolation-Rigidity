import Rigidity.Steps.S3.NotLipschitz
import Rigidity.Proofs.S3.FlipCorrector

/-!
# Proposition 3.2: finite energy for the Lipschitz bound

Step `FiniteEnergyStep` of Proposition 3.2 (preamble of the proof, corrected draft L952). By
Lemma 2.1 (`Rigidity.finite_flip_full_measure`), an almost sure property of the environment holds
almost surely for every finite mask flip of the environment, in particular for every environment in
which the bonds of a finite set `B` are closed (`closeBonds_eq_maskFlip`). Lemma 2.1 needs
`0 < p`; for `p = 0` every bond is closed almost surely and closing bonds changes nothing.
-/

namespace Rigidity.Proofs.S3

open MeasureTheory LatticeProb.Percolation Rigidity.Section3 Rigidity.Steps.S3

variable {d : ℕ}

/-- For `p = 0` every bond is closed almost surely, so closing bonds changes nothing. -/
theorem ae_closeBonds_eq_of_eq_zero (p : unitInterval) (hp0 : (p : ℝ) = 0) :
    ∀ᵐ ω ∂latticeBondLaw d p, ∀ B : Finset (Bond d), closeBonds B ω = ω := by
  have hclosed : ∀ᵐ ω ∂latticeBondLaw d p, ∀ e : Bond d, ω e = false := by
    rw [ae_all_iff]
    intro e
    have h0 : latticeBondLaw d p {ω | ω e = true} = 0 := by
      rw [latticeBondLaw_open, hp0, ENNReal.ofReal_zero]
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with ω hω
    simpa using hω
  filter_upwards [hclosed] with ω hω B
  funext e
  by_cases he : e ∈ B <;> simp [closeBonds, he, hω e]

/-- Lemma 2.1 (finite energy), closing form: for `p < 1`, an almost sure property of the
environment holds almost surely for every environment obtained by closing the bonds of a finite
set. -/
theorem ae_forall_closeBonds (p : unitInterval) (hp1 : (p : ℝ) < 1)
    {Q : Configuration d → Prop} (hQ : ∀ᵐ ω ∂latticeBondLaw d p, Q ω) :
    ∀ᵐ ω ∂latticeBondLaw d p, ∀ B : Finset (Bond d), Q (closeBonds B ω) := by
  rcases (unitInterval.nonneg p).eq_or_lt with hp0 | hp0
  · filter_upwards [hQ, ae_closeBonds_eq_of_eq_zero p hp0.symm] with ω hω hB B
    rw [hB B]
    exact hω
  obtain ⟨A, hAae, hAmeas, hA⟩ := hQ.exists_measurable_mem
  have hA1 : latticeBondLaw d p A = 1 := (prob_compl_eq_zero_iff hAmeas).1 (mem_ae_iff.1 hAae)
  have hT := finite_flip_full_measure d (latticeBondLaw d p) p hp0 hp1
    (latticeBondLaw_iIndepFun p) (latticeBondLaw_map_eval p) hAmeas hA1
  have hTae := (ae_iff_measure_eq
    (RigidityFullProduct.bond_all_masks_measurable d hAmeas).nullMeasurableSet).2
    (hT.trans measure_univ.symm)
  filter_upwards [hTae] with ω hω B
  have hfin : Set.Finite {e | (decide (e ∈ B) && ω e) = true} :=
    B.finite_toSet.subset fun e he => by
      simp only [Set.mem_setOf_eq, Bool.and_eq_true, decide_eq_true_eq] at he
      exact he.1
  have hmem := hω _ hfin
  rw [← closeBonds_eq_maskFlip] at hmem
  exact hA _ hmem

/-- `FiniteEnergyStep` (preamble of the proof of Proposition 3.2, L952): if almost surely every
corrected plane of slope `e₁` is `L`-Lipschitz, then by Lemma 2.1 the same holds almost surely
for every environment in which the bonds of a finite set are closed. -/
theorem finiteEnergyStep [NeZero d] (p : unitInterval) : FiniteEnergyStep d p := by
  intro hp1 L hLip
  exact ae_forall_closeBonds p hp1 hLip

end Rigidity.Proofs.S3
