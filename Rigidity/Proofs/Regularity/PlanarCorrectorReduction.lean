import PercolationClusterHomogenization.Proofs.Regularity.PlanarOrderZeroInput
import Rigidity.Proofs.Section5.PlanarLiteratureAdapters
import PercolationClusterHomogenization.Proofs.Regularity.PlanarCorrectorReduction

/-!
# The planar qualitative corrector input from the regularity of order one

`Rigidity.External.SupercriticalBondCorrectorInputTwo` asks, almost surely on the infinite cluster
of planar bond percolation, for a unique corrected plane of every slope normalized at a vertex,
and for a unique slope of every element of `𝒜_1`. Armstrong and Dario (arXiv:1609.09431v2),
Theorem 2 (i)–(ii) for `k = 1`, give `dim 𝒜_1 = d + 1` and the correctors. This file proves the
input (`supercriticalBondCorrectorInputTwo_of_orderOne`) from

* `ArmstrongDarioOrderZeroTwo` (Theorem 2 (iii) for `k = 0`; the Liouville theorem of order zero,
  through `Rigidity.Proofs.Section5.sublinearLiouvilleStep_two`);
* `PlanarCorrectedPlaneExistenceTwo`: every slope has a corrected plane (Theorem 2 (ii) for
  `k = 1`, with the sublinearity in the uniform norm of `IsCorrectedPlane`, which comes from
  Remark 1.1 and (1.22) of the source);
* `PlanarOrderOneDimensionTwo`: `dim 𝒜_1 ≤ 3` (Theorem 2 (i) for `k = 1`);

and the cap density of the balls of the infinite cluster (proved,
`infiniteCluster_ballVolume_capDensity`), which shows that a slope is determined by a function
(`eq_zero_of_slopeAsymptotics_zero`). Uniqueness of the normalized corrected planes follows from
the Liouville theorem of order zero; the corrected planes normalized at a vertex then depend
linearly on the slope, and `(q, a) ↦ u_q + a` is an injective linear map from a space of dimension
three into `𝒜_1`, hence onto `𝒜_1`.
-/

namespace Rigidity.Proofs.Regularity

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External Rigidity.Proofs.S2

/-- **The planar qualitative corrector input** (`SupercriticalBondCorrectorInputTwo`) from the
order-zero regularity, the existence of corrected planes and the bound `dim 𝒜_1 ≤ 3`. -/
theorem supercriticalBondCorrectorInputTwo_of_orderOne (hR3 : ArmstrongDarioOrderZeroTwo)
    (hex : PlanarCorrectedPlaneExistenceTwo) (hdim : PlanarOrderOneDimensionTwo) :
    SupercriticalBondCorrectorInputTwo := by
  classical
  intro p hpc hp1
  obtain ⟨s₀, C₀, K₀, δ, -, -, -, hδ, hcap⟩ :=
    infiniteCluster_ballVolume_capDensity (d := 2) le_rfl p hpc hp1
  obtain ⟨M, -, -, -, hMae⟩ := hcap 0
  filter_upwards [Rigidity.Proofs.Section5.sublinearLiouvilleStep_two p hpc hp1 hR3,
    hex p hpc hp1, hdim p hpc hp1, hMae] with ω hL hE hD hC h
  have hcapC : ∀ R : ℝ, ClusterBallCapDensity (uniqueInfiniteComponent h) 0 (M ω) R δ :=
    fun R => (hC h R).2
  have hslope0 : ∀ v : Fin 2 → ℝ,
      componentSlopeAsymptotics (uniqueInfiniteComponent h) v (fun _ => (0 : ℝ)) → v = 0 :=
    fun v hv => eq_zero_of_slopeAsymptotics_zero _ hδ hcapC hv
  have hliou := hL h
  -- normalized corrected planes
  have hnorm : ∀ (q : Fin 2 → ℝ) (o : uniqueInfiniteComponent h),
      ∃! u : uniqueInfiniteComponent h → ℝ,
        IsCorrectedPlane (uniqueInfiniteComponent h) q u ∧ u o = 0 := by
    intro q o
    obtain ⟨u, hu⟩ := hE h q
    have hu' := isCorrectedPlane_sub (uniqueInfiniteComponent h) hu
      (isCorrectedPlane_const (uniqueInfiniteComponent h) (u o))
    rw [sub_zero] at hu'
    refine ⟨u - fun _ => u o, ⟨hu', by simp⟩, fun v ⟨hv, hvo⟩ => ?_⟩
    have hd := isCorrectedPlane_sub (uniqueInfiniteComponent h) hv hu'
    rw [sub_self] at hd
    obtain ⟨hharm, hslope⟩ :=
      (isCorrectedPlane_iff_harmonic_and_slope_asymptotics _ _ _).mp hd
    obtain ⟨c, hc⟩ := hliou _ hharm hslope
    have hc0 : c = 0 := by
      have := hc o
      simp only [Pi.sub_apply, hvo, sub_self] at this
      linarith
    funext x
    have := hc x
    rw [hc0] at this
    simp only [Pi.sub_apply] at this ⊢
    linarith
  refine ⟨hnorm, fun u hu => ?_⟩
  have : Infinite (uniqueInfiniteComponent h) :=
    Set.infinite_coe_iff.mpr (uniqueInfiniteComponent_infinite h)
  obtain ⟨o⟩ := (inferInstance : Nonempty (uniqueInfiniteComponent h))
  -- uniqueness of the slope
  have huniq : ∀ q₁ q₂ : Fin 2 → ℝ, IsCorrectedPlane (uniqueInfiniteComponent h) q₁ u →
      IsCorrectedPlane (uniqueInfiniteComponent h) q₂ u → q₁ = q₂ := by
    intro q₁ q₂ h₁ h₂
    have hd := isCorrectedPlane_sub (uniqueInfiniteComponent h) h₁ h₂
    rw [sub_self] at hd
    have hs := hd.2
    have e : (fun _ : uniqueInfiniteComponent h => (0 : ℝ)) = 0 := rfl
    rw [← e] at hs
    exact sub_eq_zero.1 (hslope0 _ hs)
  -- the normalized corrected planes depend linearly on the slope
  set uq : (Fin 2 → ℝ) → uniqueInfiniteComponent h → ℝ := fun q =>
    Classical.choose (hnorm q o).exists with huqdef
  have huq : ∀ q, IsCorrectedPlane (uniqueInfiniteComponent h) q (uq q) ∧ uq q o = 0 :=
    fun q => Classical.choose_spec (hnorm q o).exists
  have hadd : ∀ q q', uq (q + q') = uq q + uq q' := fun q q' =>
    (hnorm (q + q') o).unique (huq (q + q'))
      ⟨isCorrectedPlane_add _ (huq q).1 (huq q').1, by simp [(huq q).2, (huq q').2]⟩
  have hsmul : ∀ (c : ℝ) q, uq (c • q) = c • uq q := fun c q =>
    (hnorm (c • q) o).unique (huq (c • q))
      ⟨isCorrectedPlane_smul _ (huq q).1 c, by simp [(huq q).2]⟩
  let Φ : ((Fin 2 → ℝ) × ℝ) →ₗ[ℝ] (uniqueInfiniteComponent h → ℝ) :=
    { toFun := fun qa => uq qa.1 + fun _ => qa.2
      map_add' := fun a b => by
        simp only [Prod.fst_add, Prod.snd_add, hadd]
        funext x; simp only [Pi.add_apply]; ring
      map_smul' := fun c a => by
        simp only [Prod.smul_fst, Prod.smul_snd, hsmul, RingHom.id_apply]
        funext x; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring }
  have hmem : ∀ a, Φ a ∈ harmonicGrowthSpace (uniqueInfiniteComponent h) 1 := fun a =>
    add_mem (huq a.1).1.1 (const_mem_harmonicGrowthSpace _ 1 a.2)
  let Ψ := LinearMap.codRestrict (harmonicGrowthSpace (uniqueInfiniteComponent h) 1) Φ hmem
  have hinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    have hΦ : uq a.1 + (fun _ => a.2) = 0 := by
      have := congrArg Subtype.val ha
      simpa [Ψ, Φ] using this
    have hcp := isCorrectedPlane_add (uniqueInfiniteComponent h) (huq a.1).1
      (isCorrectedPlane_const (uniqueInfiniteComponent h) a.2)
    rw [add_zero, hΦ] at hcp
    have hq : a.1 = 0 := hslope0 _ hcp.2
    have hu0 : uq a.1 = 0 := by
      rw [hq]
      exact (hnorm 0 o).unique (huq 0) ⟨isCorrectedPlane_const _ 0, rfl⟩
    have ha2 : a.2 = 0 := by
      have := congrFun hΦ o
      simp only [Pi.add_apply, hu0, Pi.zero_apply, zero_add] at this
      exact this
    exact Prod.ext hq ha2
  obtain ⟨hfin, hrank⟩ := hD h
  have hdom : Module.finrank ℝ ((Fin 2 → ℝ) × ℝ) = 3 := by simp
  have hge := LinearMap.finrank_le_finrank_of_injective hinj
  have heq : Module.finrank ℝ ((Fin 2 → ℝ) × ℝ) =
      Module.finrank ℝ (harmonicGrowthSpace (uniqueInfiniteComponent h) 1) := by omega
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).1 hinj
  obtain ⟨a, ha⟩ := hsurj ⟨u, hu⟩
  have hua : u = uq a.1 + fun _ => a.2 := by
    have := congrArg Subtype.val ha
    simpa [Ψ, Φ] using this.symm
  have hcp := isCorrectedPlane_add (uniqueInfiniteComponent h) (huq a.1).1
    (isCorrectedPlane_const (uniqueInfiniteComponent h) a.2)
  rw [add_zero, ← hua] at hcp
  exact ⟨a.1, hcp, fun q hq => huniq q a.1 hq hcp⟩

end Rigidity.Proofs.Regularity
