import Rigidity.Proofs.Topology.Polyomino.Main

/-!
# Lemma 2.13 in the form used at L2124

`polyominoJordan` proves `Rigidity.Section2.PolyominoJordanStmt`, the special case of Lemma 2.13
of the corrected draft that the proof of Proposition 5.12 uses at L2124: for a finite union of
closed lattice squares whose interior `𝒮` is connected, with connected complement in `S²` and all
boundary points simple, `∂𝒮` is a closed lattice polygon without repeated corner, homeomorphic
to the circle. The general Lemma 2.13 (Rudin, Remark 14.20) is not formalized.

The proof scales the plane by `1/2` and applies
`Rigidity.Proofs.Topology.Polyomino.frontier_eq_polyTrace` to the cells of side `1/2`. It uses
the planar Jordan curve theorem (`MatedCRTHarmonic.Planar.Jordan.jordan_curve_components`) and no
literature input.

No Lean proof uses this lemma: the Lean proof of Proposition 5.12 takes its Jordan loop around a
spanning tree of the connectors (`Rigidity.Proofs.Section5.JordanLoop`), not along the boundary
of the filled connector set (see `Rigidity.Steps.Section5.InfiniteDisjointPaths`).
-/

open Set Function LatticeProb LatticeProb.Percolation

namespace Rigidity.Assembly

open Rigidity.Proofs.Section5.JordanLoop Rigidity.Proofs.Topology.Polyomino Rigidity.Section2

theorem latticeSquare_eq_image {h : E2 ≃ₜ E2} (hh : ∀ q, h q = (2 : ℝ) • q) (z : Vertex 2) :
    latticeSquare z = h '' Cell (pr z) := by
  ext p
  constructor
  · intro hp
    obtain ⟨h0a, h0b⟩ := abs_le.1 (hp 0)
    obtain ⟨h1a, h1b⟩ := abs_le.1 (hp 1)
    refine ⟨(1 / 2 : ℝ) • p, ⟨?_, ?_⟩, ?_⟩
    · simp only [pr, PiLp.smul_apply, smul_eq_mul]
      rw [abs_le]; constructor <;> linarith
    · simp only [pr, PiLp.smul_apply, smul_eq_mul]
      rw [abs_le]; constructor <;> linarith
    · rw [hh, smul_smul]; norm_num
  · rintro ⟨q, ⟨h0, h1⟩, rfl⟩
    obtain ⟨h0a, h0b⟩ := abs_le.1 h0
    obtain ⟨h1a, h1b⟩ := abs_le.1 h1
    simp only [pr] at h0a h0b h1a h1b
    intro k
    fin_cases k
    · show |(h q) 0 - (z 0 : ℝ)| ≤ 1 / 2
      rw [hh, PiLp.smul_apply, smul_eq_mul, abs_le]; constructor <;> linarith
    · show |(h q) 1 - (z 1 : ℝ)| ≤ 1 / 2
      rw [hh, PiLp.smul_apply, smul_eq_mul, abs_le]; constructor <;> linarith

theorem image_segment_two {h : E2 ≃ₜ E2} (hh : ∀ q, h q = (2 : ℝ) • q) (a b : E2) :
    h '' segment ℝ a b = segment ℝ (h a) (h b) := by
  have : (⇑h) = ⇑(((2 : ℝ) • LinearMap.id : E2 →ₗ[ℝ] E2).toAffineMap) := by
    funext q
    simp [hh]
  rw [this, image_segment]

theorem two_smul_mpt {h : E2 ≃ₜ E2} (hh : ∀ q, h q = (2 : ℝ) • q) (m : ℤ × ℤ) :
    h (mpt m) = squareCorner (toV m) := by
  rw [hh]
  apply E2_ext <;> simp [mpt, squareCorner, toV] <;> ring

/-- **Lemma 2.13, in the form used at L2124 of the corrected draft** (the proof of
Proposition 5.12): the boundary of the interior of a finite union of closed lattice squares which
is connected, has connected complement in `S²` and only simple boundary points is a closed lattice
polygon without repeated corner, homeomorphic to the circle. The general Lemma 2.13 is not
formalized, and no Lean proof uses this lemma. -/
theorem polyominoJordan : PolyominoJordanStmt := by
  intro A hA σ hσ hσr Ω hΩ hconn hcompl hsimple
  obtain ⟨h, hh⟩ : ∃ h : E2 ≃ₜ E2, ∀ q, h q = (2 : ℝ) • q :=
    ⟨Homeomorph.smulOfNeZero (2 : ℝ) two_ne_zero, fun q => rfl⟩
  have hS : (pr '' A).Finite := hA.image pr
  have hU : ⋃ z ∈ A, latticeSquare z = h '' cellUnion (pr '' A) := by
    rw [cellUnion, image_iUnion₂, biUnion_image]
    exact iUnion₂_congr fun z _ => latticeSquare_eq_image hh z
  have hΩ' : Ω = h '' interior (cellUnion (pr '' A)) := by
    rw [hΩ, hU, h.image_interior]
  have hfr : frontier Ω = h '' frontier (interior (cellUnion (pr '' A))) := by
    rw [hΩ', h.image_frontier]
  have hconn' : IsConnected (interior (cellUnion (pr '' A))) := by
    have := hconn.image h.symm h.symm.continuous.continuousOn
    rwa [hΩ', image_image, show (fun x => h.symm (h x)) = id from funext h.symm_apply_apply,
      image_id] at this
  have hσ' : Topology.IsOpenEmbedding (σ ∘ h) := hσ.comp h.isOpenEmbedding
  have hσr' : range (σ ∘ h) = {northPole}ᶜ := by rw [h.surjective.range_comp, hσr]
  have hcompl' : IsConnected ((σ ∘ h) '' interior (cellUnion (pr '' A)))ᶜ := by
    rw [image_comp, ← hΩ']
    exact hcompl
  have hsimple' : ∀ x ∈ frontier (interior (cellUnion (pr '' A))),
      IsSimpleBoundaryPoint (interior (cellUnion (pr '' A))) x := by
    intro x hx
    apply IsSimpleBoundaryPoint.of_homeomorph h
    rw [← hΩ']
    exact hsimple (h x) (by rw [hfr]; exact mem_image_of_mem h hx)
  obtain ⟨⟨e⟩, M, c, hM, hcM, hadj, hinj, hpoly⟩ :=
    frontier_eq_polyTrace hS hσ' hσr' hconn' hcompl' hsimple'
  refine ⟨⟨(Homeomorph.setCongr hfr).trans
      ((h.image (frontier (interior (cellUnion (pr '' A))))).symm.trans e)⟩,
    M, fun i => toV (c i), hM, congrArg toV hcM, hadj,
    fun i j hi hj hij => hinj i j hi hj (toV_injective hij), ?_⟩
  rw [hfr, hpoly, polyTrace, image_iUnion₂]
  refine iUnion₂_congr fun i _ => ?_
  rw [image_segment_two hh, two_smul_mpt hh, two_smul_mpt hh]

end Rigidity.Assembly
