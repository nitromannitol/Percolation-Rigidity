import Rigidity.Proofs.Regularity.PlanarMesoscopicTwoTop

/-!
# The top-scale bounds in the proof of Lemma 7.3 at `k = 2` in the plane

With `T = R / (8A)`, `U = [u]_𝒫` and `G = R^{-1} inf_a R^{-1} ‖u - a‖_{ℓ²(𝒞_∞ ∩ B_R)}`
(Armstrong and Dario, arXiv:1609.09431v2, proof of Lemma 7.3, Step 2):

* `harmonicApproximation_error_le`: the harmonic approximation hypothesis of Lemma 7.2 at the
  radius `R / 2 = 4 A T` bounds the distance of `U` to the lattice harmonic functions on `B_{4T}` by
  `(4T)^{1-α} (4 S' G + K G / T)`, the coarse oscillation at `R/2` being bounded crudely through
  the largest cube side `S'`;
* `coarse_top_bounds`: if this distance is at most `B`, the excesses of `U` on `B_T` over the
  lattice harmonic quadratic functions and over the constants are at most
  `C_t B + C_a D̃_2(R) + C_b G` and `C_t B + C_a D̃_0(R)`.
-/

namespace Rigidity.Proofs.Regularity

open Finset LatticeProb LatticeProb.Percolation Rigidity.Percolation Rigidity.External

variable {ω : Configuration 2}

/-- **The harmonic approximation error at `4T`.** -/
theorem harmonicApproximation_error_le (hP : PlanarPartitionEvent ω)
    (h : HasUniqueInfiniteOpenComponent ω) (u : uniqueInfiniteComponent h → ℝ)
    {A α K X R S' : ℝ} (hA : 2 ≤ A) (hK : 0 ≤ K) (hR : 12 ≤ R) (hS'0 : 0 ≤ S')
    (hS' : S' ≤ R / 8) (hXT : X ≤ 4 * (R / (8 * A)))
    (hsize : ∀ y : Vertex 2,
      dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding (0 : Vertex 2)) < R →
        (3 : ℝ) ^ (planarPartCube ω y).scale ≤ S')
    (hHA : HarmonicApproximation (componentBallSeminorm (latticeComponent 2) 0)
      (latticeHarmonicClass 0) (clusterConstants (latticeComponent 2)) A α X (R / 2)
      (K / (R / 2) * ⨅ a : ℝ, clusterBallVolumeL2 (uniqueInfiniteComponent h) (R / 2)
        (u - fun _ => a))
      (fun x => coarseAtAnchor (uniqueInfiniteComponent h) u x.val)) :
    ballDist (componentBallSeminorm (latticeComponent 2) 0)
        (latticeHarmonicClass 0 (4 * (R / (8 * A)))) (4 * (R / (8 * A)))
        (fun x => coarseAtAnchor (uniqueInfiniteComponent h) u x.val) ≤
      (4 * (R / (8 * A))) ^ (1 - α) *
        (4 * S' * ((⨅ a : ℝ, clusterBallVolumeL2 (uniqueInfiniteComponent h) R
            (u - fun _ => a)) / R) +
          K * ((⨅ a : ℝ, clusterBallVolumeL2 (uniqueInfiniteComponent h) R
            (u - fun _ => a)) / R) / (R / (8 * A))) := by
  have hA0 : 0 < A := by linarith
  have hR0 : 0 < R := by linarith
  set T := R / (8 * A) with hT
  have hT0 : 0 < T := by positivity
  set D0R := ⨅ a : ℝ, clusterBallVolumeL2 (uniqueInfiniteComponent h) R (u - fun _ => a)
    with hD0R
  have hD0R0 : 0 ≤ D0R := iInf_nonneg_of_nonneg fun _ => clusterBallVolumeL2_nonneg' _ _ _
  set U : latticeComponent 2 → ℝ := fun x => coarseAtAnchor (uniqueInfiniteComponent h) u x.val
    with hU
  have h4T : 4 * T ≤ R / 2 / A := by
    rw [hT, le_div_iff₀ hA0]; field_simp; linarith
  have hHA' := hHA (4 * T) hXT h4T
  have hAT : A * (4 * T) = R / 2 := by rw [hT]; field_simp; ring
  rw [hAT] at hHA'
  have hsup := iSup_Icc_self_le (f := fun s => ballExcess (componentBallSeminorm
    (latticeComponent 2) 0) (clusterConstants (latticeComponent 2)) s U / s) (R / 2)
  -- the crude bound of the coarse oscillation at `R/2`
  have hcrude : ballExcess (componentBallSeminorm (latticeComponent 2) 0)
      (clusterConstants (latticeComponent 2)) (R / 2) U ≤ 0 + 2 * S' * D0R := by
    apply le_add_mul_iInf (by positivity)
    intro c
    have hc : (fun _ : latticeComponent 2 => c) ∈ clusterConstants (latticeComponent 2) :=
      ⟨c, fun _ => rfl⟩
    have h1 := ballExcess_le (componentBallSeminorm (latticeComponent 2) 0)
      (clusterConstants (latticeComponent 2)) (s := R / 2) (u := U) hc
    rw [componentBallSeminorm_apply] at h1
    have h2 := componentBallL2_coarse_sub_const_le hP h u (ρ := R / 2) (R := R) (S := S')
      (by linarith) hS'0
      (fun y hy => (anchor_bounds hP hS' le_rfl (mem_latticeBallPoints.1 hy)
        (hsize y ((mem_latticeBallPoints.1 hy).trans (by linarith)))).1)
      (fun y hy => pow_le_pow_left₀ (by positivity)
        (hsize y ((mem_latticeBallPoints.1 hy).trans (by linarith))) 2) c
    have e : S' * R / (R / 2) = 2 * S' := by field_simp
    rw [e] at h2
    calc ballExcess (componentBallSeminorm (latticeComponent 2) 0)
          (clusterConstants (latticeComponent 2)) (R / 2) U
        ≤ componentBallL2 (latticeComponent 2) 0 (R / 2) (U - fun _ => c) := h1
      _ ≤ 2 * S' * clusterBallVolumeL2 (uniqueInfiniteComponent h) R (u - fun _ => c) := h2
      _ = 0 + 2 * S' * clusterBallVolumeL2 (uniqueInfiniteComponent h) R (u - fun _ => c) := by
          ring
  -- the oscillation at `R/2`
  have hosc : (⨅ a : ℝ, clusterBallVolumeL2 (uniqueInfiniteComponent h) (R / 2)
      (u - fun _ => a)) ≤ 0 + 2 * D0R := by
    apply le_add_mul_iInf (by norm_num)
    intro c
    have h1 := iInf_le_of_le (f := fun a : ℝ => clusterBallVolumeL2 (uniqueInfiniteComponent h)
      (R / 2) (u - fun _ => a)) (fun _ => clusterBallVolumeL2_nonneg' _ _ _) c
    have h2 := clusterBallVolumeL2_le_of_le' (uniqueInfiniteComponent h) (by linarith : 0 < R / 2)
      (by linarith : R / 2 ≤ R) (u - fun _ => c)
    have e : R / (R / 2) = 2 := by field_simp
    rw [e] at h2
    linarith
  have hrpow : 0 ≤ (4 * T) ^ (1 - α) := Real.rpow_nonneg (by positivity) _
  refine hHA'.trans (mul_le_mul_of_nonneg_left ?_ hrpow)
  have hE : K / (R / 2) * (⨅ a : ℝ, clusterBallVolumeL2 (uniqueInfiniteComponent h) (R / 2)
      (u - fun _ => a)) / (4 * T) ≤ K * (D0R / R) / T := by
    have hK' : 0 ≤ K / (R / 2) := by positivity
    have := mul_le_mul_of_nonneg_left hosc hK'
    rw [div_le_iff₀ (by positivity)]
    calc K / (R / 2) * (⨅ a : ℝ, clusterBallVolumeL2 (uniqueInfiniteComponent h) (R / 2)
          (u - fun _ => a)) ≤ K / (R / 2) * (0 + 2 * D0R) := this
      _ = K * (D0R / R) / T * (4 * T) := by field_simp; ring
  have hS : ballExcess (componentBallSeminorm (latticeComponent 2) 0)
      (clusterConstants (latticeComponent 2)) (R / 2) U / (R / 2) ≤ 4 * S' * (D0R / R) := by
    rw [div_le_iff₀ (by positivity)]
    calc _ ≤ 0 + 2 * S' * D0R := hcrude
      _ = 4 * S' * (D0R / R) * (R / 2) := by field_simp; ring
  have := hsup.trans hS
  linarith

/-- The constant `C_t` of `coarse_top_bounds`. -/
noncomputable def coarseTopConst : ℝ :=
  Real.sqrt ((5 * (6 * Real.sqrt ((2 : ℕ) : ℝ))) ^ 2 / 1) * 4 + 17179873280 * 100

theorem coarseTopConst_nonneg : 0 ≤ coarseTopConst := by unfold coarseTopConst; positivity

/-- **One harmonic quadratic polynomial at the top scale.** -/
theorem coarse_top_one (hP : PlanarPartitionEvent ω) (h : HasUniqueInfiniteOpenComponent ω)
    (u : uniqueInfiniteComponent h → ℝ) {A K₁ K₂ R S' B η : ℝ} (hA : 2 ≤ A) (hK₂ : 0 ≤ K₂)
    (hR : 512 * A ≤ R) (hS' : S' ≤ R / 8)
    (hsize : ∀ y : Vertex 2,
      dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding (0 : Vertex 2)) < R →
        (3 : ℝ) ^ (planarPartCube ω y).scale ≤ S')
    (hm₁ : ∑ y ∈ latticeBallPoints 0 R, (3 : ℝ) ^ (planarPartCube ω y).scale ≤ K₁ * R ^ 2)
    (hm₂ : ∑ y ∈ latticeBallPoints 0 R, ((3 : ℝ) ^ (planarPartCube ω y).scale) ^ 2 ≤ K₂ * R ^ 2)
    {v : latticeComponent 2 → ℝ} (hvm : v ∈ latticeHarmonicClass (0 : Vertex 2)
      (4 * (R / (8 * A))))
    (hvb : componentBallL2 (latticeComponent 2) 0 (4 * (R / (8 * A)))
      ((fun x => coarseAtAnchor (uniqueInfiniteComponent h) u x.val) - v) ≤ B + η)
    (a : ℝ) (p : EuclideanSpace ℝ (Fin 2)) {M : Matrix (Fin 2) (Fin 2) ℝ} (hM : M.trace = 0) :
    componentBallL2 (latticeComponent 2) 0 (R / (8 * A))
        (fun x => coarseAtAnchor (uniqueInfiniteComponent h) u x.val -
          latticeQuadFun a p M x.val) ≤
      coarseTopConst * (B + η) + 17179873280 * (64 * A ^ 2) * (Real.sqrt K₂ *
          clusterBallVolumeL2 (uniqueInfiniteComponent h) R
            (u - fun x => latticeQuadFun a p M x.val)) +
        17179873280 * (64 * A ^ 2) * (2 * K₁) *
          ((|p 0| + |p 1| + 2 * (|M 0 0| + |M 0 1 + M 1 0| + |M 1 1|) * R) * R) / R := by
  have hA0 : 0 < A := by linarith
  have hR0 : 0 < R := by linarith
  set T := R / (8 * A) with hT
  have hT64 : 64 ≤ T := by rw [hT, le_div_iff₀ (by positivity)]; linarith
  have hT0 : 0 < T := by linarith
  have h4T : 4 * T ≤ R / 2 := by
    rw [hT]; rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  set C₁ : ℝ := 17179873280 * (64 * A ^ 2) with hC₁
  have hCMV : (17179873280 : ℝ) / T ^ 2 = C₁ / R ^ 2 := by
    rw [hT, hC₁]; field_simp; ring
  have h1 := componentBallL2_coarse_sub_quad_le (coarseAtAnchor (uniqueInfiniteComponent h) u)
    hT64 hvm a p hM
  have h2 := sum_abs_coarse_sub_quad_top_le hP h u (ρ := 4 * T) hR0 hS' h4T hsize hm₁ hm₂ a p M
  have hsq : Real.sqrt (K₂ * R ^ 2) = Real.sqrt K₂ * R := by
    rw [Real.sqrt_mul hK₂, Real.sqrt_sq hR0.le]
  rw [hsq] at h2
  rw [hCMV] at h1
  set E := clusterBallVolumeL2 (uniqueInfiniteComponent h) R
    (u - fun x => latticeQuadFun a p M x.val) with hE
  set Λ := |p 0| + |p 1| + 2 * (|M 0 0| + |M 0 1 + M 1 0| + |M 1 1|) * R with hΛ
  set S₄ := ∑ y ∈ latticeBallPoints 0 (4 * T),
    |coarseAtAnchor (uniqueInfiniteComponent h) u y - latticeQuadFun a p M y| with hS₄
  have hC₁0 : 0 ≤ C₁ := by positivity
  have h3 : C₁ / R ^ 2 * S₄ ≤ C₁ * (Real.sqrt K₂ * E) + C₁ * (2 * K₁) * (Λ * R) / R := by
    have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ C₁ / R ^ 2)
    refine this.trans (le_of_eq ?_)
    field_simp
  have hfirst := mul_le_mul_of_nonneg_left hvb coarseTopConst_nonneg
  have h1' : componentBallL2 (latticeComponent 2) 0 T
      (fun x => coarseAtAnchor (uniqueInfiniteComponent h) u x.val - latticeQuadFun a p M x.val) ≤
      coarseTopConst * componentBallL2 (latticeComponent 2) 0 (4 * T)
        ((fun x => coarseAtAnchor (uniqueInfiniteComponent h) u x.val) - v) + C₁ / R ^ 2 * S₄ :=
    h1
  linarith

/-- **The top-scale bounds.** -/
theorem coarse_top_bounds {A K₁ K₂ κ : ℝ} (hA : 2 ≤ A) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hκ : 0 < κ) :
    ∃ Ca Cb : ℝ, 0 ≤ Ca ∧ 0 ≤ Cb ∧ ∀ (ω : Configuration 2) (hP : PlanarPartitionEvent ω)
      (h : HasUniqueInfiniteOpenComponent ω) (ℓ R S' B : ℝ) (u : uniqueInfiniteComponent h → ℝ),
      512 * A ≤ R → quadLocality 2 (capFraction 2 κ) * max ℓ 1 ≤ R → S' ≤ R / 8 →
      (∀ y : Vertex 2,
        dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding (0 : Vertex 2)) < R →
          (3 : ℝ) ^ (planarPartCube ω y).scale ≤ S') →
      (∑ y ∈ latticeBallPoints 0 R, (3 : ℝ) ^ (planarPartCube ω y).scale ≤ K₁ * R ^ 2) →
      (∑ y ∈ latticeBallPoints 0 R, ((3 : ℝ) ^ (planarPartCube ω y).scale) ^ 2 ≤ K₂ * R ^ 2) →
      ClusterCubeDensity (uniqueInfiniteComponent h) 0 (quadLocality 2 (capFraction 2 κ)) ℓ κ →
      ballDist (componentBallSeminorm (latticeComponent 2) 0)
          (latticeHarmonicClass (0 : Vertex 2) (4 * (R / (8 * A)))) (4 * (R / (8 * A)))
          (fun x => coarseAtAnchor (uniqueInfiniteComponent h) u x.val) ≤ B →
      ballExcess (componentBallSeminorm (latticeComponent 2) 0) (latticeHarmonicQuadratic 2)
          (R / (8 * A)) (fun x => coarseAtAnchor (uniqueInfiniteComponent h) u x.val) ≤
        coarseTopConst * B + Ca * (⨅ w : clusterHarmonicQuadratic (uniqueInfiniteComponent h),
            clusterBallVolumeL2 (uniqueInfiniteComponent h) R (u - w)) +
          Cb * ((⨅ a : ℝ, clusterBallVolumeL2 (uniqueInfiniteComponent h) R
            (u - fun _ => a)) / R) ∧
      ballExcess (componentBallSeminorm (latticeComponent 2) 0)
          (clusterConstants (latticeComponent 2))
          (R / (8 * A)) (fun x => coarseAtAnchor (uniqueInfiniteComponent h) u x.val) ≤
        coarseTopConst * B + Ca * (⨅ a : ℝ, clusterBallVolumeL2 (uniqueInfiniteComponent h) R
            (u - fun _ => a)) := by
  set Kc := 2 * quadCoeffConst κ * Real.sqrt (72 / κ) with hKc
  have hKc0 : 0 ≤ Kc := by have := quadCoeffConst_nonneg hκ; positivity
  set C₁ : ℝ := 17179873280 * (64 * A ^ 2) with hC₁
  have hC₁0 : 0 ≤ C₁ := by positivity
  refine ⟨C₁ * (Real.sqrt K₂ + 2 * K₁ * Kc), C₁ * (2 * K₁ * Kc), by positivity, by positivity,
    ?_⟩
  intro ω hP h ℓ R S' B u hR hRq hS' hsize hm₁ hm₂ hcube hB
  have hA0 : 0 < A := by linarith
  have hR0 : 0 < R := by linarith
  have hR1 : 1 ≤ R := by linarith
  set T := R / (8 * A) with hT
  set U : latticeComponent 2 → ℝ := fun x => coarseAtAnchor (uniqueInfiniteComponent h) u x.val
    with hU
  set D0R := ⨅ a : ℝ, clusterBallVolumeL2 (uniqueInfiniteComponent h) R (u - fun _ => a)
    with hD0R
  have hD0R0 : 0 ≤ D0R := iInf_nonneg_of_nonneg fun _ => clusterBallVolumeL2_nonneg' _ _ _
  have hCt := coarseTopConst_nonneg
  -- a near approximant at `4T`
  have hv : ∀ η : ℝ, 0 < η → ∃ v ∈ latticeHarmonicClass (0 : Vertex 2) (4 * T),
      componentBallL2 (latticeComponent 2) 0 (4 * T) (U - v) ≤ B + η := by
    intro η hη
    haveI : Nonempty (latticeHarmonicClass (0 : Vertex 2) (4 * T)) :=
      ⟨⟨0, zero_mem_latticeHarmonicClass (0 : Vertex 2) (4 * T)⟩⟩
    obtain ⟨v, hv⟩ := exists_lt_of_ciInf_lt (lt_add_of_pos_right
      (ballDist (componentBallSeminorm (latticeComponent 2) 0)
        (latticeHarmonicClass (0 : Vertex 2) (4 * T)) (4 * T) U) hη)
    refine ⟨v, v.2, ?_⟩
    rw [← componentBallSeminorm_apply]
    exact hv.le.trans (by linarith)
  constructor
  · -- `k = 2`
    apply le_of_forall_pos_le_add_mul hCt
    intro η hη
    obtain ⟨v, hvm, hvb⟩ := hv η hη
    have key : ∀ w : clusterHarmonicQuadratic (uniqueInfiniteComponent h),
        ballExcess (componentBallSeminorm (latticeComponent 2) 0) (latticeHarmonicQuadratic 2)
            T U ≤ (coarseTopConst * B + C₁ * (2 * K₁ * Kc) * (D0R / R) + coarseTopConst * η) +
          C₁ * (Real.sqrt K₂ + 2 * K₁ * Kc) *
            clusterBallVolumeL2 (uniqueInfiniteComponent h) R (u - w) := by
      intro w
      obtain ⟨a, p, M, hM, hw⟩ := w.2
      have hwe : (w : uniqueInfiniteComponent h → ℝ) = fun x => latticeQuadFun a p M x.val :=
        funext fun x => hw x
      rw [hwe]
      have hwl := mem_latticeHarmonicQuadratic_of_trace_eq_zero a p hM
      have h0 := ballExcess_le (componentBallSeminorm (latticeComponent 2) 0)
        (latticeHarmonicQuadratic 2) (s := T) (u := U) hwl
      rw [componentBallSeminorm_apply] at h0
      have h1 := coarse_top_one hP h u hA hK₂ hR hS' hsize hm₁ hm₂ hvm hvb a p hM
      have hslope := slope_le_of_clusterCubeDensity (uniqueInfiniteComponent h) hκ hcube hRq
        a p M u
      rw [← hKc, ← hD0R] at hslope
      set E := clusterBallVolumeL2 (uniqueInfiniteComponent h) R
        (u - fun x => latticeQuadFun a p M x.val) with hE
      have hE0 : 0 ≤ E := clusterBallVolumeL2_nonneg' _ _ _
      set ΛR := (|p 0| + |p 1| + 2 * (|M 0 0| + |M 0 1 + M 1 0| + |M 1 1|) * R) * R with hΛR
      have hc0 : 0 ≤ C₁ * (2 * K₁) := by positivity
      have hthird : C₁ * (2 * K₁) * ΛR / R ≤
          C₁ * (2 * K₁ * Kc) * (D0R / R) + C₁ * (2 * K₁ * Kc) * E := by
        have h5 := mul_le_mul_of_nonneg_left hslope hc0
        have h6 : C₁ * (2 * K₁) * ΛR / R ≤ C₁ * (2 * K₁) * (Kc * (D0R + E)) / R :=
          div_le_div_of_nonneg_right h5 hR0.le
        refine h6.trans ?_
        have h7 : C₁ * (2 * K₁) * (Kc * (D0R + E)) / R =
            C₁ * (2 * K₁ * Kc) * (D0R / R) + C₁ * (2 * K₁ * Kc) * (E / R) := by
          field_simp
        rw [h7]
        have h8 : E / R ≤ E := div_le_self hE0 hR1
        have h9 := mul_le_mul_of_nonneg_left h8 (by positivity : (0 : ℝ) ≤ C₁ * (2 * K₁ * Kc))
        linarith
      have hU0 : componentBallL2 (latticeComponent 2) 0 T
          (U - fun x => latticeQuadFun a p M x.val) =
          componentBallL2 (latticeComponent 2) 0 (R / (8 * A))
            (fun x => coarseAtAnchor (uniqueInfiniteComponent h) u x.val -
              latticeQuadFun a p M x.val) := rfl
      rw [hU0] at h0
      have e1 : C₁ * (Real.sqrt K₂ + 2 * K₁ * Kc) * E =
          C₁ * (Real.sqrt K₂ * E) + C₁ * (2 * K₁ * Kc) * E := by ring
      rw [e1]
      linarith
    have := le_add_mul_iInf (by positivity : (0 : ℝ) ≤ C₁ * (Real.sqrt K₂ + 2 * K₁ * Kc)) key
    linarith
  · -- `k = 0`
    apply le_of_forall_pos_le_add_mul hCt
    intro η hη
    obtain ⟨v, hvm, hvb⟩ := hv η hη
    have key : ∀ c : ℝ,
        ballExcess (componentBallSeminorm (latticeComponent 2) 0)
          (clusterConstants (latticeComponent 2)) T U ≤
          (coarseTopConst * B + coarseTopConst * η) +
            C₁ * (Real.sqrt K₂ + 2 * K₁ * Kc) *
              clusterBallVolumeL2 (uniqueInfiniteComponent h) R (u - fun _ => c) := by
      intro c
      have hc : (fun _ : latticeComponent 2 => c) ∈ clusterConstants (latticeComponent 2) :=
        ⟨c, fun _ => rfl⟩
      have h0 := ballExcess_le (componentBallSeminorm (latticeComponent 2) 0)
        (clusterConstants (latticeComponent 2)) (s := T) (u := U) hc
      rw [componentBallSeminorm_apply] at h0
      have hq : ∀ y : Vertex 2, latticeQuadFun c 0 0 y = c := fun y => by
        simp [latticeQuadFun, quadForm]
      have h1 := coarse_top_one hP h u hA hK₂ hR hS' hsize hm₁ hm₂ hvm hvb c 0 (M := 0)
        (by simp)
      have hU0 : componentBallL2 (latticeComponent 2) 0 T (U - fun _ => c) =
          componentBallL2 (latticeComponent 2) 0 (R / (8 * A))
            (fun x => coarseAtAnchor (uniqueInfiniteComponent h) u x.val -
              latticeQuadFun c 0 0 x.val) := by
        congr 1; funext x; simp only [Pi.sub_apply, hq, hU]
      have hE : clusterBallVolumeL2 (uniqueInfiniteComponent h) R
          (u - fun x => latticeQuadFun c 0 0 x.val) =
          clusterBallVolumeL2 (uniqueInfiniteComponent h) R (u - fun _ => c) := by
        congr 1; funext x; simp only [Pi.sub_apply, hq]
      rw [hE] at h1
      rw [hU0] at h0
      have hzero : (|(0 : EuclideanSpace ℝ (Fin 2)) 0| + |(0 : EuclideanSpace ℝ (Fin 2)) 1| +
          2 * (|(0 : Matrix (Fin 2) (Fin 2) ℝ) 0 0| +
            |(0 : Matrix (Fin 2) (Fin 2) ℝ) 0 1 + (0 : Matrix (Fin 2) (Fin 2) ℝ) 1 0| +
            |(0 : Matrix (Fin 2) (Fin 2) ℝ) 1 1|) * R) * R = 0 := by simp
      rw [hzero, mul_zero, zero_div, add_zero] at h1
      set E := clusterBallVolumeL2 (uniqueInfiniteComponent h) R (u - fun _ => c)
      have hE0 : 0 ≤ E := clusterBallVolumeL2_nonneg' _ _ _
      have hCa'' : C₁ * (Real.sqrt K₂ * E) ≤ C₁ * (Real.sqrt K₂ + 2 * K₁ * Kc) * E := by
        have : 0 ≤ C₁ * (2 * K₁ * Kc) * E := by positivity
        nlinarith
      linarith
    have := le_add_mul_iInf (by positivity : (0 : ℝ) ≤ C₁ * (Real.sqrt K₂ + 2 * K₁ * Kc)) key
    linarith

end Rigidity.Proofs.Regularity
