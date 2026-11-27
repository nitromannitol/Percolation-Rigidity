import Rigidity.Proofs.Green.GaussianShiftSumD
import Rigidity.Proofs.Green.PointSourceFinalD

/-!
# From the point source in `ℓ²` to the heat kernel at a pair of points

For `x, y ∈ K` and `s > 0`, `p_{2s}(x, y) = Σ_z p_s(z, x) p_s(z, y)`; replacing both columns by the
normalized Gaussians `G^x_s, G^y_s` costs `‖p^x - G^x‖ ‖p^y‖ + ‖G^x‖ ‖p^y - G^y‖`
(`abs_tsum_mul_le_l2norm`), and by the product of Gaussian kernels

  `Σ_z G^x_s(z) G^y_s(z) = (M^x_s M^y_s)^{-1} p̄(2s, x - y) Σ_{z ∈ K} p̄(s/2, z - m)`

with `m` the midpoint of `x` and `y` (`tsum_clusterInd_mul_clusterInd`). The last sum is the
Gaussian mass `M_{s/2}` of the cluster at the lattice point `x ⊓ y` nearest to `m` (`midLattice`)
up to `K_ρ (s/2)^{-1/2}` (`tsum_abs_gaussianHeatD_shift_le`). The resulting bound is
`abs_vsrwHeat_sub_gaussianHeatD_le`.
-/

open scoped Classical
open LatticeProb.Percolation

namespace Rigidity.Green

variable {d : ℕ}

/-- **Cauchy–Schwarz**: `|Σ f g| ≤ ‖f‖ ‖g‖`. -/
theorem abs_tsum_mul_le_l2norm {V : Type*} {f g : V → ℝ} (hf : Summable fun x => f x ^ 2)
    (hg : Summable fun x => g x ^ 2) : |∑' x, f x * g x| ≤ l2norm f * l2norm g := by
  have h := sq_le_mul_of_hasSum (summable_mul_of_sq' hf hg).hasSum hf.hasSum hg.hasSum
  rw [← Real.sqrt_sq_eq_abs, l2norm, l2norm, ← Real.sqrt_mul (tsum_nonneg fun _ => sq_nonneg _)]
  exact Real.sqrt_le_sqrt h

/-- The lattice point nearest (coordinatewise below) to the midpoint of `x` and `y`. -/
def midLattice (x y : Vertex d) : Vertex d := fun i => (x i + y i) / 2

/-- The midpoint of `x` and `y` in `ℝ^d`. -/
noncomputable def midPoint (x y : Vertex d) : EuclideanSpace ℝ (Fin d) :=
  (1 / 2 : ℝ) • (latticeEuclideanEmbedding x + latticeEuclideanEmbedding y)

theorem abs_coord_midPoint_sub_le (x y : Vertex d) (i : Fin d) :
    |(midPoint x y - latticeEuclideanEmbedding (midLattice x y)) i| ≤ 1 / 2 := by
  have e : (midPoint x y - latticeEuclideanEmbedding (midLattice x y)) i =
      ((x i : ℝ) + y i) / 2 - (((x i + y i) / 2 : ℤ) : ℝ) := by
    simp only [midPoint, PiLp.sub_apply, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
    change 1 / 2 * ((x i : ℝ) + (y i : ℝ)) - (((x i + y i) / 2 : ℤ) : ℝ) = _
    ring
  rw [e]
  have h1 : x i + y i = 2 * ((x i + y i) / 2) + (x i + y i) % 2 := by omega
  have h2 : (x i + y i) % 2 = 0 ∨ (x i + y i) % 2 = 1 := by omega
  set q := (x i + y i) / 2
  set r := (x i + y i) % 2
  have hq : ((x i : ℝ) + y i) = 2 * (q : ℝ) + r := by
    have h3 : ((x i + y i : ℤ) : ℝ) = ((2 * q + r : ℤ) : ℝ) := by rw [← h1]
    push_cast at h3
    linarith
  rw [hq]
  rcases h2 with h | h <;> rw [h] <;> push_cast <;> ring_nf <;> norm_num

theorem norm_midPoint_sub_le (x y : Vertex d) :
    ‖midPoint x y - latticeEuclideanEmbedding (midLattice x y)‖ ≤ d := by
  set v := midPoint x y - latticeEuclideanEmbedding (midLattice x y)
  rw [EuclideanSpace.norm_eq]
  have h : ∑ i, ‖v i‖ ^ 2 ≤ (d : ℝ) ^ 2 := by
    calc ∑ i, ‖v i‖ ^ 2 ≤ ∑ _i : Fin d, (1 : ℝ) := Finset.sum_le_sum fun i _ => by
          rw [Real.norm_eq_abs, sq_abs]
          have := abs_coord_midPoint_sub_le x y i
          nlinarith [abs_nonneg (v i), sq_abs (v i)]
      _ = d := by simp
      _ ≤ (d : ℝ) ^ 2 := by
          rcases Nat.eq_zero_or_pos d with h0 | h0
          · simp [h0]
          · have : (1 : ℝ) ≤ d := by exact_mod_cast h0
            nlinarith
  calc Real.sqrt (∑ i, ‖v i‖ ^ 2) ≤ Real.sqrt ((d : ℝ) ^ 2) := Real.sqrt_le_sqrt h
    _ = d := Real.sqrt_sq (Nat.cast_nonneg d)

variable {ω : Configuration d} {K : OpenComponent ω} {σ : ℝ}

/-- **The product of the Gaussians of two poles on the cluster.** -/
theorem tsum_clusterInd_mul_clusterInd (hσ : 0 < σ) {s : ℝ} (hs : 0 < s) (x y : Vertex d) :
    ∑' z, clusterInd K σ s x z * clusterInd K σ s y z =
      gaussianHeatD d σ (2 * s) (edzD x y) *
        ∑' z, (if z ∈ K.supp then
          gaussianHeatD d σ (s / 2) (latticeEuclideanEmbedding z - midPoint x y) else 0) := by
  rw [← tsum_mul_left]
  refine tsum_congr fun z => ?_
  unfold clusterInd
  split_ifs with hz
  · rw [gaussianHeatD_mul_gaussianHeatD hσ hs]
    have e1 : edzD z x - edzD z y = -edzD x y := by simp only [edzD]; abel
    have e2 : (1 / 2 : ℝ) • (edzD z x + edzD z y) = latticeEuclideanEmbedding z - midPoint x y := by
      simp only [edzD, midPoint, smul_add, smul_sub]
      module
    rw [e1, e2]
    unfold gaussianHeatD
    rw [norm_neg]
  · simp

/-- `|S/(M_x M_y) - θ^{-1}| ≤ 4 (e_S + e_x + 2 e_y)/θ²` for masses within `θ/2` of `θ`. -/
theorem abs_div_mul_sub_inv_le {θ S Mx My eS ex ey : ℝ} (hθ : 0 < θ) (hS : |S - θ| ≤ eS)
    (hx : |Mx - θ| ≤ ex) (hy : |My - θ| ≤ ey) (hx2 : ex ≤ θ / 2) (hy2 : ey ≤ θ / 2) :
    |S / (Mx * My) - θ⁻¹| ≤ 4 * (eS + ex + 2 * ey) / θ ^ 2 := by
  have hx' := abs_le.1 hx
  have hy' := abs_le.1 hy
  have hMx : θ / 2 ≤ Mx := by linarith
  have hMy : θ / 2 ≤ My := by linarith
  have hMx2 : Mx ≤ 2 * θ := by linarith
  have hMx0 : 0 < Mx := by linarith
  have hMy0 : 0 < My := by linarith
  have e : S / (Mx * My) - θ⁻¹ =
      (θ * (S - θ) + θ * (θ - Mx) + Mx * (θ - My)) / (θ * (Mx * My)) := by
    field_simp; ring
  rw [e, abs_div, abs_of_pos (by positivity : 0 < θ * (Mx * My))]
  have hnum : |θ * (S - θ) + θ * (θ - Mx) + Mx * (θ - My)| ≤ θ * (eS + ex + 2 * ey) := by
    have h1 : |θ * (S - θ)| ≤ θ * eS := by rw [abs_mul, abs_of_pos hθ]; gcongr
    have h2 : |θ * (θ - Mx)| ≤ θ * ex := by
      rw [abs_mul, abs_of_pos hθ, abs_sub_comm]; gcongr
    have h3 : |Mx * (θ - My)| ≤ 2 * θ * ey := by
      rw [abs_mul, abs_of_pos hMx0, abs_sub_comm]
      exact mul_le_mul hMx2 hy (abs_nonneg _) (by linarith)
    calc _ ≤ |θ * (S - θ) + θ * (θ - Mx)| + |Mx * (θ - My)| := abs_add_le _ _
      _ ≤ |θ * (S - θ)| + |θ * (θ - Mx)| + |Mx * (θ - My)| := by
          gcongr; exact abs_add_le _ _
      _ ≤ θ * eS + θ * ex + 2 * θ * ey := by linarith
      _ = _ := by ring
  have hden : θ * (θ / 2 * (θ / 2)) ≤ θ * (Mx * My) := by
    apply mul_le_mul_of_nonneg_left _ hθ.le
    exact mul_le_mul hMx hMy (by positivity) hMx0.le
  have hE0 : 0 ≤ eS + ex + 2 * ey := by
    have := (abs_nonneg _).trans hS
    have := (abs_nonneg _).trans hx
    have := (abs_nonneg _).trans hy
    linarith
  calc _ ≤ θ * (eS + ex + 2 * ey) / (θ * (Mx * My)) :=
        div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ θ * (eS + ex + 2 * ey) / (θ * (θ / 2 * (θ / 2))) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = _ := by field_simp; ring

variable [NeZero d]

/-- **The heat kernel at a pair of points** from the point source at both poles, Proposition A.7
at the poles and at `midLattice x y`, and the move of the centre of the Gaussian. -/
theorem abs_vsrwHeat_sub_gaussianHeatD_le (hσ : 0 < σ) {θ : ℝ} (hθ : 0 < θ) {s : ℝ} (hs : 2 ≤ s)
    {x y : Vertex d} {Ex Ey Py Gx ex ey e' : ℝ}
    (hEx : l2norm (fun z => vsrwHeat (openGraph ω) (2 * d) s z x - clusterGaussNorm K σ s x z) ≤ Ex)
    (hEy : l2norm (fun z => vsrwHeat (openGraph ω) (2 * d) s z y - clusterGaussNorm K σ s y z) ≤ Ey)
    (hPy : l2norm (fun z => vsrwHeat (openGraph ω) (2 * d) s z y) ≤ Py)
    (hGx : l2norm (clusterGaussNorm K σ s x) ≤ Gx)
    (hAx : |clusterGaussMass K σ s x - θ| ≤ ex) (hAy : |clusterGaussMass K σ s y - θ| ≤ ey)
    (hx2 : ex ≤ θ / 2) (hy2 : ey ≤ θ / 2)
    (hA' : |clusterGaussMass K σ (s / 2) (midLattice x y) - θ| ≤ e') :
    |vsrwHeat (openGraph ω) (2 * d) (2 * s) x y - θ⁻¹ * gaussianHeatD d σ (2 * s) (edzD x y)| ≤
      Ex * Py + Gx * Ey + gaussianHeatD d σ (2 * s) (edzD x y) *
        (4 * (e' + shiftConstD d σ d * (s / 2) ^ (-(1 / 2 : ℝ)) + ex + 2 * ey) / θ ^ 2) := by
  have hD := two_mul_pos_d (d := d)
  have hdeg := openGraph_degree_le ω
  have hs0 : 0 < s := by linarith
  set px : Vertex d → ℝ := fun z => vsrwHeat (openGraph ω) (2 * d) s z x with hpx
  set py : Vertex d → ℝ := fun z => vsrwHeat (openGraph ω) (2 * d) s z y with hpy
  set gx := clusterGaussNorm K σ s x with hgx
  set gy := clusterGaussNorm K σ s y with hgy
  have hpx2 : Summable fun z => px z ^ 2 := summable_sq_vsrwHeat_col hD hdeg hs0.le x
  have hpy2 : Summable fun z => py z ^ 2 := summable_sq_vsrwHeat_col hD hdeg hs0.le y
  have hgx2 : Summable fun z => gx z ^ 2 := summable_sq_clusterGaussNorm hσ hs0
  have hgy2 : Summable fun z => gy z ^ 2 := summable_sq_clusterGaussNorm hσ hs0
  -- the semigroup property
  have hsg : vsrwHeat (openGraph ω) (2 * d) (2 * s) x y = ∑' z, px z * py z := by
    rw [show 2 * s = s + s by ring, ← (hasSum_vsrwHeat_mul hD hdeg hs0.le hs0.le x y).tsum_eq]
    exact tsum_congr fun z => by
      simp only [hpx, hpy]
      rw [vsrwHeat_symm hD hdeg s x z]
  -- the two replacements
  have hsplit : ∑' z, px z * py z - ∑' z, gx z * gy z =
      ∑' z, (px z - gx z) * py z + ∑' z, gx z * (py z - gy z) := by
    have h1 := summable_mul_of_sq' hpx2 hpy2
    have h2 := summable_mul_of_sq' hgx2 hgy2
    have h3 := summable_mul_of_sq' (summable_sq_sub_l2 hpx2 hgx2) hpy2
    have h4 := summable_mul_of_sq' hgx2 (summable_sq_sub_l2 hpy2 hgy2)
    rw [← h1.tsum_sub h2, ← h3.tsum_add h4]
    exact tsum_congr fun z => by ring
  have hcs1 := abs_tsum_mul_le_l2norm (summable_sq_sub_l2 hpx2 hgx2) hpy2
  have hcs2 := abs_tsum_mul_le_l2norm hgx2 (summable_sq_sub_l2 hpy2 hgy2)
  have hrep : |∑' z, px z * py z - ∑' z, gx z * gy z| ≤ Ex * Py + Gx * Ey := by
    rw [hsplit]
    calc _ ≤ |∑' z, (px z - gx z) * py z| + |∑' z, gx z * (py z - gy z)| := abs_add_le _ _
      _ ≤ l2norm (fun z => px z - gx z) * l2norm py + l2norm gx * l2norm (fun z => py z - gy z) :=
          add_le_add hcs1 hcs2
      _ ≤ Ex * Py + Gx * Ey :=
          add_le_add (mul_le_mul hEx hPy (l2norm_nonneg _) ((l2norm_nonneg _).trans hEx))
            (mul_le_mul hGx hEy (l2norm_nonneg _) ((l2norm_nonneg _).trans hGx))
  -- the Gaussian part
  set b := gaussianHeatD d σ (2 * s) (edzD x y) with hb
  have hb0 : 0 ≤ b := gaussianHeatD_nonneg' σ (2 * s) (by positivity) _
  set S := ∑' z, (if z ∈ K.supp then
    gaussianHeatD d σ (s / 2) (latticeEuclideanEmbedding z - midPoint x y) else 0) with hS
  have hgg : ∑' z, gx z * gy z =
      b * S / (clusterGaussMass K σ s x * clusterGaussMass K σ s y) := by
    have e : ∀ z, gx z * gy z = (clusterGaussMass K σ s x * clusterGaussMass K σ s y)⁻¹ *
        (clusterInd K σ s x z * clusterInd K σ s y z) := fun z => by
      simp only [hgx, hgy, clusterGaussNorm]
      rw [div_mul_div_comm, div_eq_inv_mul]
    rw [tsum_congr e, tsum_mul_left, tsum_clusterInd_mul_clusterInd hσ hs0 x y]
    ring
  -- the move of the centre
  have hshift := tsum_abs_gaussianHeatD_shift_le (d := d) hσ (by linarith : 1 ≤ s / 2)
    (Nat.cast_nonneg d) (midLattice x y) (midPoint x y) (norm_midPoint_sub_le x y)
  have hSM : |S - clusterGaussMass K σ (s / 2) (midLattice x y)| ≤
      shiftConstD d σ d * (s / 2) ^ (-(1 / 2 : ℝ)) := by
    have hm1 : Summable fun z => (if z ∈ K.supp then
        gaussianHeatD d σ (s / 2) (latticeEuclideanEmbedding z - midPoint x y) else 0) := by
      have h0 := summable_gaussianHeatD (d := d) hσ (by linarith : (0 : ℝ) < s / 2)
        (midLattice x y)
      refine (h0.add hshift.1).of_nonneg_of_le (fun z => by
        split_ifs
        · exact gaussianHeatD_nonneg' σ (s / 2) (by positivity) _
        · exact le_rfl) (fun z => ?_)
      split_ifs
      · have := le_abs_self
          (gaussianHeatD d σ (s / 2) (latticeEuclideanEmbedding z - midPoint x y) -
            gaussianHeatD d σ (s / 2) (edzD z (midLattice x y)))
        linarith
      · exact add_nonneg (gaussianHeatD_nonneg' σ (s / 2) (by positivity) _) (abs_nonneg _)
    have hm2 := summable_clusterInd (K := K) (y := midLattice x y) hσ
      (by linarith : (0 : ℝ) < s / 2)
    rw [hS, clusterGaussMass, ← hm1.tsum_sub hm2]
    calc _ ≤ ∑' z, |(if z ∈ K.supp then
          gaussianHeatD d σ (s / 2) (latticeEuclideanEmbedding z - midPoint x y) else 0) -
          clusterInd K σ (s / 2) (midLattice x y) z| := by
          have hs' : Summable fun z => ‖(if z ∈ K.supp then
              gaussianHeatD d σ (s / 2) (latticeEuclideanEmbedding z - midPoint x y) else 0) -
              clusterInd K σ (s / 2) (midLattice x y) z‖ := by
            refine hshift.1.of_nonneg_of_le (fun z => norm_nonneg _) (fun z => ?_)
            unfold clusterInd
            rw [Real.norm_eq_abs]
            split_ifs <;> simp
          calc _ = ‖∑' z, ((if z ∈ K.supp then
                gaussianHeatD d σ (s / 2) (latticeEuclideanEmbedding z - midPoint x y) else 0) -
                clusterInd K σ (s / 2) (midLattice x y) z)‖ := (Real.norm_eq_abs _).symm
            _ ≤ _ := norm_tsum_le_tsum_norm hs'
            _ = _ := tsum_congr fun z => Real.norm_eq_abs _
      _ ≤ ∑' z, |gaussianHeatD d σ (s / 2) (latticeEuclideanEmbedding z - midPoint x y) -
          gaussianHeatD d σ (s / 2) (edzD z (midLattice x y))| := by
          refine Summable.tsum_le_tsum (fun z => ?_) ?_ hshift.1
          · unfold clusterInd
            split_ifs <;> simp
          · refine hshift.1.of_nonneg_of_le (fun z => abs_nonneg _) (fun z => ?_)
            unfold clusterInd
            split_ifs <;> simp
      _ ≤ _ := hshift.2
  have hSθ : |S - θ| ≤ e' + shiftConstD d σ d * (s / 2) ^ (-(1 / 2 : ℝ)) := by
    calc |S - θ| ≤ |S - clusterGaussMass K σ (s / 2) (midLattice x y)| +
        |clusterGaussMass K σ (s / 2) (midLattice x y) - θ| := abs_sub_le _ _ _
      _ ≤ _ := by linarith
  have hratio := abs_div_mul_sub_inv_le hθ hSθ hAx hAy hx2 hy2
  have hgauss : |∑' z, gx z * gy z - θ⁻¹ * b| ≤
      b * (4 * (e' + shiftConstD d σ d * (s / 2) ^ (-(1 / 2 : ℝ)) + ex + 2 * ey) / θ ^ 2) := by
    rw [hgg]
    have e : b * S / (clusterGaussMass K σ s x * clusterGaussMass K σ s y) - θ⁻¹ * b =
        b * (S / (clusterGaussMass K σ s x * clusterGaussMass K σ s y) - θ⁻¹) := by ring
    rw [e, abs_mul, abs_of_nonneg hb0]
    exact mul_le_mul_of_nonneg_left hratio hb0
  rw [hsg]
  calc _ ≤ |∑' z, px z * py z - ∑' z, gx z * gy z| + |∑' z, gx z * gy z - θ⁻¹ * b| :=
        abs_sub_le _ _ _
    _ ≤ _ := add_le_add hrep hgauss

end Rigidity.Green
