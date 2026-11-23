import Rigidity.Proofs.Regularity.PlanarQuadraticLipschitz
import Rigidity.Proofs.Regularity.LatticeKIterationTwo
import Rigidity.Proofs.Regularity.LatticeHarmonicMeanValue
import Rigidity.Proofs.Regularity.OrderZeroLiouville

/-!
# Steps of the proof of Lemma 7.3 at `k = 2` in the plane

The steps of the proof of Lemma 7.3 of Armstrong and Dario (arXiv:1609.09431v2) which pass between
`u` on the infinite cluster `C` of a planar configuration and its coarsening
`U = [u]_𝒫` (`coarseAtAnchor`) on the balls of `ℤ²`, with `D̃_k(r)` the excess of `u` over the
harmonic polynomials of degree `k` in the normalization `r^{-1} ‖·‖_{ℓ²(C ∩ B_r)}`
(`clusterBallVolumeL2`) and `D_k(r)` the excess of `U` on the lattice ball:

* `clusterExcess_two_le`, `clusterExcess_zero_le` (Step 1, (7.21)):
  `D̃_k(r) ≤ r^{-1} ‖u - U‖_{ℓ²(C ∩ B_r)} + 3 D_k(r)`, the lattice harmonic quadratic functions
  restricting to harmonic quadratic polynomials of the cluster;
* `componentBallL2_coarse_sub_quad_le` (the passage from (7.19) to (7.20)
  through (7.11), and Step 2, (7.22)–(7.23), at the top scale `T`): for a lattice
  harmonic function `v` on `B_{4T}` and a harmonic quadratic polynomial `W`,
  `‖U - W‖_{L̲²(B_T)} ≤ C ‖U - v‖_{L̲²(B_{4T})} + C T^{-2} ∑_{B_{4T}} |U - W|`, by the `ℓ^∞`–`ℓ¹`
  bound of lattice harmonic functions applied to `v - W`; the sum is bounded by
  `sum_abs_coarse_sub_le`;
* `ballExcess_zero_le_of_crude`: the crude bound of the coarse oscillation at the top scale.
-/

namespace Rigidity.Proofs.Regularity

open Finset LatticeProb LatticeProb.Percolation Rigidity.Percolation Rigidity.External

variable {ω : Configuration 2}

/-- **Infimum bound.** -/
theorem le_add_mul_iInf {ι : Type*} [Nonempty ι] {f : ι → ℝ} {X a C : ℝ}
    (hC : 0 ≤ C) (h : ∀ i, X ≤ a + C * f i) : X ≤ a + C * ⨅ i, f i := by
  by_contra hlt
  push Not at hlt
  rcases hC.eq_or_lt with h0 | hpos
  · obtain ⟨i⟩ := ‹Nonempty ι›
    have h1 := h i
    rw [← h0, zero_mul, add_zero] at h1 hlt
    linarith
  · have hlt' : ⨅ i, f i < (X - a) / C := by rw [lt_div_iff₀ hpos]; linarith
    obtain ⟨i, hi⟩ := exists_lt_of_ciInf_lt hlt'
    have h1 := h i
    rw [lt_div_iff₀ hpos] at hi
    linarith

theorem iInf_nonneg_of_nonneg {ι : Type*} {f : ι → ℝ} (hf : ∀ i, 0 ≤ f i) : 0 ≤ ⨅ i, f i := by
  rcases isEmpty_or_nonempty ι with h | h
  · rw [Real.iInf_of_isEmpty]
  · exact le_ciInf hf

theorem iInf_le_of_le {ι : Type*} {f : ι → ℝ} (hf : ∀ i, 0 ≤ f i) (i : ι) : ⨅ i, f i ≤ f i :=
  ciInf_le ⟨0, fun _ ⟨j, hj⟩ => hj ▸ hf j⟩ i

theorem IsHarmonicInBall.mono' {C : OpenComponent ω} {R R' : ℝ} {u : C → ℝ}
    (h : IsHarmonicInBall C R u) (hR : R' ≤ R) : IsHarmonicInBall C R' u :=
  fun x hx hnb => h x (componentEuclideanBall_mono C 0 hR hx)
    fun y hy => componentEuclideanBall_mono C 0 hR (hnb y hy)

theorem clusterBallVolumeL2_nonneg' (C : OpenComponent ω) (r : ℝ) (f : C → ℝ) :
    0 ≤ clusterBallVolumeL2 C r f :=
  Real.sqrt_nonneg _

/-- The normalized cluster norm on a smaller ball. -/
theorem clusterBallVolumeL2_le_of_le' (C : OpenComponent ω) {s R : ℝ} (hs : 0 < s) (hsR : s ≤ R)
    (f : C → ℝ) : clusterBallVolumeL2 C s f ≤ R / s * clusterBallVolumeL2 C R f := by
  have hR : 0 < R := hs.trans_le hsR
  have hsum : ∑ x ∈ componentEuclideanBall C 0 s, f x ^ 2 ≤
      ∑ x ∈ componentEuclideanBall C 0 R, f x ^ 2 :=
    sum_le_sum_of_subset_of_nonneg (componentEuclideanBall_mono C 0 hsR)
      fun _ _ _ => sq_nonneg _
  rw [clusterBallVolumeL2, clusterBallVolumeL2]
  have hK : 0 ≤ R / s * Real.sqrt ((∑ x ∈ componentEuclideanBall C 0 R, f x ^ 2) / R ^ 2) := by
    positivity
  rw [Real.sqrt_le_left hK, mul_pow, Real.sq_sqrt (div_nonneg (sum_nonneg fun _ _ => sq_nonneg _)
    (by positivity)), div_pow]
  calc (∑ x ∈ componentEuclideanBall C 0 s, f x ^ 2) / s ^ 2
      ≤ (∑ x ∈ componentEuclideanBall C 0 R, f x ^ 2) / s ^ 2 :=
        div_le_div_of_nonneg_right hsum (by positivity)
    _ = R ^ 2 / s ^ 2 * ((∑ x ∈ componentEuclideanBall C 0 R, f x ^ 2) / R ^ 2) := by
        field_simp

theorem clusterBallVolumeL2_add_le' (C : OpenComponent ω) (r : ℝ) (f g : C → ℝ) :
    clusterBallVolumeL2 C r (f + g) ≤ clusterBallVolumeL2 C r f + clusterBallVolumeL2 C r g := by
  rcases le_or_gt r 0 with hr | hr
  · simp [clusterBallVolumeL2, componentEuclideanBall_eq_empty C 0 hr]
  · rw [clusterBallVolumeL2_eq C hr.le, clusterBallVolumeL2_eq C hr.le,
      clusterBallVolumeL2_eq C hr.le, ← mul_add]
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    have := (componentBallSeminorm C 0 r).add_le' f g
    simpa [componentBallSeminorm_apply] using this

/-- **Step 1 at `k = 2`.** -/
theorem clusterExcess_two_le (h : HasUniqueInfiniteOpenComponent ω)
    (u : uniqueInfiniteComponent h → ℝ) {r : ℝ} (hr : 3 ≤ r) :
    (⨅ w : clusterHarmonicQuadratic (uniqueInfiniteComponent h),
        clusterBallVolumeL2 (uniqueInfiniteComponent h) r (u - w)) ≤
      clusterBallVolumeL2 (uniqueInfiniteComponent h) r
          (u - fun x => coarseAtAnchor (uniqueInfiniteComponent h) u x.val) +
        3 * ballExcess (componentBallSeminorm (latticeComponent 2) 0) (latticeHarmonicQuadratic 2)
          r (fun x => coarseAtAnchor (uniqueInfiniteComponent h) u x.val) := by
  apply le_add_mul_iInf (by norm_num)
  rintro ⟨wl, hwl⟩
  obtain ⟨a, p, M, hwl', hmem⟩ :=
    mem_clusterHarmonicQuadratic_of_mem_latticeHarmonicQuadratic (uniqueInfiniteComponent h) hwl
  set w : uniqueInfiniteComponent h → ℝ := fun x => latticeQuadFun a p M x.val with hw
  set U : Vertex 2 → ℝ := coarseAtAnchor (uniqueInfiniteComponent h) u with hU
  have h1 := iInf_le_of_le (f := fun w : clusterHarmonicQuadratic (uniqueInfiniteComponent h) =>
    clusterBallVolumeL2 (uniqueInfiniteComponent h) r (u - w))
    (fun _ => clusterBallVolumeL2_nonneg' _ _ _) ⟨w, hmem⟩
  have e : u - w = (u - fun x => U x.val) + fun x => (fun y => U y - latticeQuadFun a p M y) x.val := by
    funext x; simp only [Pi.sub_apply, Pi.add_apply, hw]; ring
  have h2 := clusterBallVolumeL2_add_le' (uniqueInfiniteComponent h) r (u - fun x => U x.val)
    (fun x => (fun y => U y - latticeQuadFun a p M y) x.val)
  have h3 := clusterBallVolumeL2_le_three_mul (uniqueInfiniteComponent h) hr
    (fun y => U y - latticeQuadFun a p M y)
  have e2 : componentBallL2 (latticeComponent 2) 0 r
      (fun x => (fun y => U y - latticeQuadFun a p M y) x.val) =
      componentBallSeminorm (latticeComponent 2) 0 r ((fun x => U x.val) - wl) := by
    rw [componentBallSeminorm_apply]
    congr 1
    funext x
    simp only [Pi.sub_apply, hwl' x]
  rw [e2] at h3
  calc (⨅ w : clusterHarmonicQuadratic (uniqueInfiniteComponent h),
        clusterBallVolumeL2 (uniqueInfiniteComponent h) r (u - w))
      ≤ clusterBallVolumeL2 (uniqueInfiniteComponent h) r (u - w) := h1
    _ ≤ _ := by rw [e]; linarith

/-- **Step 1 at `k = 0`.** -/
theorem clusterExcess_zero_le (h : HasUniqueInfiniteOpenComponent ω)
    (u : uniqueInfiniteComponent h → ℝ) {r : ℝ} (hr : 3 ≤ r) :
    (⨅ a : ℝ, clusterBallVolumeL2 (uniqueInfiniteComponent h) r (u - fun _ => a)) ≤
      clusterBallVolumeL2 (uniqueInfiniteComponent h) r
          (u - fun x => coarseAtAnchor (uniqueInfiniteComponent h) u x.val) +
        3 * ballExcess (componentBallSeminorm (latticeComponent 2) 0)
          (clusterConstants (latticeComponent 2))
          r (fun x => coarseAtAnchor (uniqueInfiniteComponent h) u x.val) := by
  apply le_add_mul_iInf (by norm_num)
  rintro ⟨wl, c, hc⟩
  set U : Vertex 2 → ℝ := coarseAtAnchor (uniqueInfiniteComponent h) u with hU
  have h1 := iInf_le_of_le (f := fun a : ℝ =>
    clusterBallVolumeL2 (uniqueInfiniteComponent h) r (u - fun _ => a))
    (fun _ => clusterBallVolumeL2_nonneg' _ _ _) c
  have e : (u - fun _ => c) = (u - fun x => U x.val) + fun x => (fun y => U y - c) x.val := by
    funext x; simp only [Pi.sub_apply, Pi.add_apply]; ring
  have h2 := clusterBallVolumeL2_add_le' (uniqueInfiniteComponent h) r (u - fun x => U x.val)
    (fun x => (fun y => U y - c) x.val)
  have h3 := clusterBallVolumeL2_le_three_mul (uniqueInfiniteComponent h) hr (fun y => U y - c)
  have e2 : componentBallL2 (latticeComponent 2) 0 r (fun x => (fun y => U y - c) x.val) =
      componentBallSeminorm (latticeComponent 2) 0 r ((fun x => U x.val) - wl) := by
    rw [componentBallSeminorm_apply]
    congr 1
    funext x
    simp only [Pi.sub_apply, hc x]
  rw [e2] at h3
  calc (⨅ a : ℝ, clusterBallVolumeL2 (uniqueInfiniteComponent h) r (u - fun _ => a))
      ≤ clusterBallVolumeL2 (uniqueInfiniteComponent h) r (u - fun _ => c) := h1
    _ ≤ _ := by rw [e]; linarith

/-- The radius factor on the balls of `ℤ²`: `‖f‖_{L̲²(B_s)} ≤ √1800 (r / s) ‖f‖_{L̲²(B_r)}` for
`6 √2 ≤ s ≤ r`. -/
theorem componentBallL2_lattice_le (f : latticeComponent 2 → ℝ) {s r : ℝ}
    (hs : 6 * Real.sqrt ((2 : ℕ) : ℝ) ≤ s) (hsr : s ≤ r) :
    componentBallL2 (latticeComponent 2) 0 s f ≤
      Real.sqrt ((5 * (6 * Real.sqrt ((2 : ℕ) : ℝ))) ^ 2 / 1) * (r / s) *
        componentBallL2 (latticeComponent 2) 0 r f := by
  have hvol := clusterBallVolumeComparison_of_clusterCubeDensity (latticeComponent 2) 0 r
    (by norm_num) one_pos (clusterCubeDensity_latticeComponent 0 (24 * Real.sqrt ((2 : ℕ) : ℝ)) 1)
  have hX : (0 : ℝ) < 6 * Real.sqrt ((2 : ℕ) : ℝ) * max 1 1 := by positivity
  have hmono := radiusMonotone_componentBallSeminorm (latticeComponent 2) 0 hX (by positivity)
    hvol f s r (by rw [max_self, mul_one]; exact hs) hsr le_rfl
  rw [componentBallSeminorm_apply, componentBallSeminorm_apply] at hmono
  have e : (r / s) ^ (((2 : ℕ) : ℝ) / 2) = r / s := by norm_num
  rwa [e] at hmono

/-- `∑ |f| ≤ (card) ‖f‖_{L̲²}` on a cluster ball. -/
theorem sum_abs_le_card_mul_componentBallL2 (C : OpenComponent ω) (z : Vertex 2) (r : ℝ)
    (f : C → ℝ) :
    ∑ x ∈ componentEuclideanBall C z r, |f x| ≤
      ((componentEuclideanBall C z r).card : ℝ) * componentBallL2 C z r f := by
  have hcs := sq_sum_le_card_mul_sum_sq (s := componentEuclideanBall C z r)
    (f := fun x => |f x|)
  simp only [sq_abs] at hcs
  rw [sum_sq_eq_card_mul_componentBallL2_sq] at hcs
  set n := ((componentEuclideanBall C z r).card : ℝ)
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hN0 := componentBallL2_nonneg C z r f
  have h0 : 0 ≤ ∑ x ∈ componentEuclideanBall C z r, |f x| := sum_nonneg fun _ _ => abs_nonneg _
  have hsq : (∑ x ∈ componentEuclideanBall C z r, |f x|) ^ 2 ≤
      (n * componentBallL2 C z r f) ^ 2 := by
    rw [mul_pow]; nlinarith
  nlinarith [mul_nonneg hn0 hN0]

/-- **The mean value step at the top scale.** -/
theorem componentBallL2_harmonic_sub_quad_le {F : (Fin 2 → ℤ) → ℝ} {T : ℝ} (hT : 64 ≤ T)
    (hF : ∀ y : Fin 2 → ℤ, dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding 0) <
      4 * T → latticeLaplacian F y = 0) (a : ℝ) (p : EuclideanSpace ℝ (Fin 2))
    {M : Matrix (Fin 2) (Fin 2) ℝ} (hM : M.trace = 0) :
    componentBallL2 (latticeComponent 2) 0 T (fun x => F x.val - latticeQuadFun a p M x.val) ≤
      17179873280 / T ^ 2 * ∑ x ∈ componentEuclideanBall (latticeComponent 2) 0 (4 * T),
        |F x.val - latticeQuadFun a p M x.val| := by
  have hg : ∀ y : Fin 2 → ℤ, dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding 0) <
      4 * T → latticeLaplacian (fun y => F y - latticeQuadFun a p M y) y = 0 := by
    intro y hy
    rw [latticeLaplacian_sub, hF y hy, latticeLaplacian_latticeQuadFun, hM, mul_zero, sub_zero]
  exact componentBallL2_le_sum_abs_of_latticeHarmonic (fun y => F y - latticeQuadFun a p M y)
    0 hT hg

/-- **Step 2 at the top scale.** For `v` lattice harmonic on `B_{4T}` and `W = a + ⟪p, ·⟫ + q_M`
with `tr M = 0`, `‖U - W‖_{L̲²(B_T)} ≤ C₁ ‖U - v‖_{L̲²(B_{4T})} + C_MV T^{-2} ∑_{B_{4T}} |U - W|`. -/
theorem componentBallL2_coarse_sub_quad_le (U : Vertex 2 → ℝ) {T : ℝ} (hT : 64 ≤ T)
    {v : latticeComponent 2 → ℝ} (hv : v ∈ latticeHarmonicClass 0 (4 * T)) (a : ℝ)
    (p : EuclideanSpace ℝ (Fin 2)) {M : Matrix (Fin 2) (Fin 2) ℝ} (hM : M.trace = 0) :
    componentBallL2 (latticeComponent 2) 0 T (fun x => U x.val - latticeQuadFun a p M x.val) ≤
      (Real.sqrt ((5 * (6 * Real.sqrt ((2 : ℕ) : ℝ))) ^ 2 / 1) * 4 + 17179873280 * 100) *
          componentBallL2 (latticeComponent 2) 0 (4 * T) ((fun x : latticeComponent 2 => U x.val) - v) +
        17179873280 / T ^ 2 * ∑ y ∈ latticeBallPoints 0 (4 * T),
          |U y - latticeQuadFun a p M y| := by
  classical
  obtain ⟨F, hvF, hF⟩ := hv
  have hT0 : 0 < T := by linarith
  have hN₄0 := componentBallL2_nonneg (latticeComponent 2) 0 (4 * T) ((fun x : latticeComponent 2 => U x.val) - v)
  -- the triangle inequality
  have e : (fun x : latticeComponent 2 => U x.val - latticeQuadFun a p M x.val) =
      ((fun x : latticeComponent 2 => U x.val) - v) + fun x => F x.val - latticeQuadFun a p M x.val := by
    funext x
    show U x.val - latticeQuadFun a p M x.val =
      (U x.val - v x) + (F x.val - latticeQuadFun a p M x.val)
    rw [hvF x]; ring
  have htri := map_add_le_add (componentBallSeminorm (latticeComponent 2) 0 T)
    ((fun x : latticeComponent 2 => U x.val) - v) (fun x => F x.val - latticeQuadFun a p M x.val)
  rw [← e, componentBallSeminorm_apply, componentBallSeminorm_apply,
    componentBallSeminorm_apply] at htri
  -- the first term
  have hs2 : 6 * Real.sqrt ((2 : ℕ) : ℝ) ≤ T := by
    have : Real.sqrt ((2 : ℕ) : ℝ) ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
    linarith
  have h1 := componentBallL2_lattice_le ((fun x : latticeComponent 2 => U x.val) - v) hs2
    (by linarith : T ≤ 4 * T)
  have e4 : 4 * T / T = 4 := by field_simp
  rw [e4] at h1
  -- the second term
  have h2 := componentBallL2_harmonic_sub_quad_le hT hF a p hM
  have hpt : ∀ x : latticeComponent 2, |F x.val - latticeQuadFun a p M x.val| ≤
      |((fun x : latticeComponent 2 => U x.val) - v) x| + |U x.val - latticeQuadFun a p M x.val| := fun x => by
    have : F x.val - latticeQuadFun a p M x.val = -((fun x : latticeComponent 2 => U x.val) - v) x +
        (U x.val - latticeQuadFun a p M x.val) := by
      show F x.val - latticeQuadFun a p M x.val = -(U x.val - v x) +
        (U x.val - latticeQuadFun a p M x.val)
      rw [hvF x]; ring
    rw [this]
    exact (abs_add_le _ _).trans (by rw [abs_neg])
  have hs1 : ∑ x ∈ componentEuclideanBall (latticeComponent 2) 0 (4 * T),
      |F x.val - latticeQuadFun a p M x.val| ≤
      ∑ x ∈ componentEuclideanBall (latticeComponent 2) 0 (4 * T), |((fun x : latticeComponent 2 => U x.val) - v) x| +
        ∑ y ∈ latticeBallPoints 0 (4 * T), |U y - latticeQuadFun a p M y| := by
    rw [← sum_latticeBallPoints 0 (4 * T) (fun y => |U y - latticeQuadFun a p M y|),
      ← sum_add_distrib]
    exact sum_le_sum fun x _ => hpt x
  have hS1 := sum_abs_le_card_mul_componentBallL2 (latticeComponent 2) 0 (4 * T)
    ((fun x : latticeComponent 2 => U x.val) - v)
  have hncard : ((componentEuclideanBall (latticeComponent 2) 0 (4 * T)).card : ℝ) ≤
      100 * T ^ 2 := by
    have := card_componentEuclideanBall_le (latticeComponent 2) 0 (by linarith : (0 : ℝ) ≤ 4 * T)
    calc _ ≤ (2 * (4 * T) + 3) ^ 2 := this
      _ ≤ 100 * T ^ 2 := by nlinarith
  set N₄ := componentBallL2 (latticeComponent 2) 0 (4 * T) ((fun x : latticeComponent 2 => U x.val) - v)
  set S₂ := ∑ y ∈ latticeBallPoints 0 (4 * T), |U y - latticeQuadFun a p M y|
  have hsum : ∑ x ∈ componentEuclideanBall (latticeComponent 2) 0 (4 * T),
      |F x.val - latticeQuadFun a p M x.val| ≤ 100 * T ^ 2 * N₄ + S₂ := by
    have := mul_le_mul_of_nonneg_right hncard hN₄0
    linarith
  have hC : (0 : ℝ) ≤ 17179873280 / T ^ 2 := by positivity
  have hfinal := h2.trans (mul_le_mul_of_nonneg_left hsum hC)
  have hT2 : 17179873280 / T ^ 2 * (100 * T ^ 2 * N₄ + S₂) =
      17179873280 * 100 * N₄ + 17179873280 / T ^ 2 * S₂ := by
    field_simp
  rw [hT2] at hfinal
  have hK : 0 ≤ Real.sqrt ((5 * (6 * Real.sqrt ((2 : ℕ) : ℝ))) ^ 2 / 1) := Real.sqrt_nonneg _
  nlinarith

end Rigidity.Proofs.Regularity
