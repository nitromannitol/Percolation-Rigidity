import Rigidity.Proofs.Topology.SphereComponents

/-!
# The Jordan curve theorem on the sphere

A simple closed path omits a point of the sphere. Stereographic projection at that point takes
it to a planar Jordan curve, and the two planar components transfer back to the sphere.
See A. Hatcher, *Algebraic Topology* (2002), Proposition 2B.1 and the remark following it,
and H. Maehara, Amer. Math. Monthly 91 (1984), 641–643.
-/

open Set Metric Bornology

namespace Rigidity.Topology

open Rigidity.External MatedCRTHarmonic.Planar.Jordan

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

/-- The Jordan curve theorem for a simple closed path on the two-sphere. -/
theorem jordan_curve_theorem_sphere : Rigidity.External.JordanCurveTheoremSphere := by
  intro q β hβ
  obtain ⟨p, hp⟩ := exists_sphere_point_not_mem_range β hβ
  let e := stereographic' 2 p
  let f := closedPathCircle β
  have hf : Continuous f := continuous_closedPathCircle β
  have hfi : Function.Injective f := injective_closedPathCircle β hβ
  have hsource (c : Circle) : f c ∈ e.source := by
    rw [stereographic'_source]
    simp only [mem_compl_iff, mem_singleton_iff]
    intro heq
    apply hp
    rw [← heq, ← range_closedPathCircle β]
    exact mem_range_self c
  let r : sphere (0 : Plane) 1 → Plane := fun t => e (f (Arcs.spherePlaneHomeoCircle t))
  have hr : Continuous r := e.continuousOn.comp_continuous
    (hf.comp Arcs.spherePlaneHomeoCircle.continuous) (fun t => hsource _)
  have hri : Function.Injective r := by
    intro a b hab
    apply Arcs.spherePlaneHomeoCircle.injective
    apply hfi
    apply e.injOn (hsource _) (hsource _)
    exact hab
  obtain ⟨x₁, hx₁, x₀, hx₀, hb, hu, hd, hcover, hf₁, hf₀⟩ :=
    jordan_curve_components r hr hri
  let U := connectedComponentIn (range r)ᶜ x₁
  let V := connectedComponentIn (range r)ᶜ x₀
  have hJopen : IsOpen (range r)ᶜ := (isCompact_range hr).isClosed.isOpen_compl
  have hUo : IsOpen U := hJopen.connectedComponentIn
  have hVo : IsOpen V := hJopen.connectedComponentIn
  have hUc : IsConnected U := isConnected_connectedComponentIn_iff.mpr hx₁
  have hVc : IsConnected V := isConnected_connectedComponentIn_iff.mpr hx₀
  have himg : e.symm '' range r = range β := by
    rw [← range_closedPathCircle β]
    change e.symm '' range r = range f
    ext z
    constructor
    · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
      exact ⟨Arcs.spherePlaneHomeoCircle t, (e.left_inv (hsource _)).symm⟩
    · rintro ⟨c, rfl⟩
      refine ⟨r (Arcs.spherePlaneHomeoCircle.symm c), ⟨_, rfl⟩, ?_⟩
      change e.symm (e (f (Arcs.spherePlaneHomeoCircle (Arcs.spherePlaneHomeoCircle.symm c)))) = f c
      rw [Homeomorph.apply_symm_apply]
      exact e.left_inv (hsource c)
  obtain ⟨A, B, hAo, hBo, hAc, hBc, hAB, hABcover, hAf, hBf⟩ :=
    sphere_components_of_plane p (range r) U V hUo hVo hUc hVc hb hu hd hcover.symm hf₁ hf₀
  rw [himg] at hABcover hAf hBf
  exact ⟨A, B, hAo, hBo, hAc, hBc, hAB, hABcover, hAf, hBf⟩

end Rigidity.Topology
