import Rigidity.Proofs.S3.PlanarFlipCorrector

/-!
# Comparison of planar corrected planes

The corrected-plane comparison uses the planar qualitative corrector and Green-column inputs.
-/

namespace Rigidity.Steps.S3

open MeasureTheory LatticeProb.Percolation Rigidity.Section3

/-- Corrected-plane comparison from the planar corrector and Green-column events. -/
theorem compareDifferentPlanes_of_green_event_two (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hcorr : Rigidity.External.SupercriticalBondCorrectorInputTwo)
    (hgreen : ∀ᵐ ω ∂latticeBondLaw 2 p,
      ∃ _h : HasUniqueInfiniteOpenComponent ω,
        ∀ h' : HasUniqueInfiniteOpenComponent ω, ∀ y : uniqueInfiniteComponent h',
          ∃! g : uniqueInfiniteComponent h' → ℝ,
            IsGreenColumn 2 le_rfl (uniqueInfiniteComponent h') y g)
    (hcluster : FlipClusterStep 2) (hflip : FlipCorrectorStep 2 p)
    (hlap : GreenLaplacianStep 2 le_rfl) (hsub : GreenColumnSublinearStep 2 le_rfl)
    (hliou : SublinearLiouvilleStep 2 p) :
    Section3.CompareDifferentPlanesStmt 2 le_rfl p := by
  filter_upwards [hgreen,
    hcorr p hpc hp1, hflip, hliou] with ω hGω hCω hFω hLω
  obtain ⟨h, hGh⟩ := hGω
  refine ⟨h, fun B hB hconn => ?_⟩
  obtain ⟨h', hsupp⟩ := hcluster ω h B hconn
  obtain ⟨o, ho⟩ := (uniqueInfiniteComponent_infinite h).nonempty
  have ho' : o ∈ (uniqueInfiniteComponent h').supp := by rw [hsupp]; exact ho
  refine ⟨h', hsupp, ⟨fun y => (hGh h y).exists.choose,
    fun y => (hGh h y).exists.choose_spec⟩, fun q => ?_⟩
  obtain ⟨hex, hun⟩ := correctedPlane_exists_unique_add_const _ q ⟨o, ho⟩ ((hCω h).1 q ⟨o, ho⟩)
  obtain ⟨hex', hun'⟩ := correctedPlane_exists_unique_add_const _ q ⟨o, ho'⟩ (hFω B h' q ⟨o, ho'⟩)
  refine ⟨hex, hun, hex', hun', fun u u' hu hu' G hG a b _ => ?_⟩
  obtain ⟨hhu, hsu⟩ := (isCorrectedPlane_iff_harmonic_and_slope_asymptotics _ q u).1 hu
  obtain ⟨hhu', hsu'⟩ := (isCorrectedPlane_iff_harmonic_and_slope_asymptotics _ q u').1 hu'
  have hharm : ∀ z, componentLaplacian (uniqueInfiniteComponent h)
      (fun x => u x - extend _ u' x.val - ∑ e ∈ B,
        greenDipole (greenFunction _ G) (extend _ u') x.val e.val) z = 0 := by
    intro z
    have hlapz := hlap ω _ B hB _ hsupp u' hhu' G hG z
    rw [show (fun x => u x - extend _ u' x.val - ∑ e ∈ B,
        greenDipole (greenFunction _ G) (extend _ u') x.val e.val) =
        fun x => u x - (extend _ u' x.val + ∑ e ∈ B,
          greenDipole (greenFunction _ G) (extend _ u') x.val e.val) from
      funext fun x => by ring, componentLaplacian_sub, hlapz, hhu z, sub_zero]
  have hsl := componentSlopeAsymptotics_sub _
    (componentSlopeAsymptotics_sub _ hsu (componentSlopeAsymptotics_extend hsupp hsu'))
    (componentSlopeAsymptotics_zero_sum _ B _
      fun e he => greenDipole_sublinear hsub _ G hG (extend _ u') e.val (hB e he).2)
  rw [sub_self, sub_zero] at hsl
  obtain ⟨c, hc⟩ := hLω h _ hharm hsl
  have ha := hc a
  have hb := hc b
  show _ = ∑ e ∈ B, compareSummand (greenFunction _ G) (extend _ u') a.val b.val e.val
  simp only [compareSummand_eq_greenDipole_sub, Finset.sum_sub_distrib]
  linarith

end Rigidity.Steps.S3
