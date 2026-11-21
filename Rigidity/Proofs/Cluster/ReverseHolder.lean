import Rigidity.Proofs.Cluster.Caccioppoli
import Mathlib.Analysis.MeanInequalities

/-!
# The reverse Hölder inequality on clusters, deterministic part

Armstrong–Dario, *Elliptic regularity and quantitative homogenization on percolation clusters*
(Comm. Pure Appl. Math. 2018), Lemma 3.6. For an exponent `s > (d+2)/2` with Hölder conjugate `s'`,
on scales where the partition `𝒫` satisfies the moment bound
`|□_m|⁻¹ ∑_{x ∈ □_{m+1}} size(□_𝒫(x))^{2sd} ≤ C`, every `u ∈ 𝒜(𝒞_*(□_{m+1}))` satisfies

`(|□_m|⁻¹ ∫_{𝒞_*(□_m)} |∇u 1_{𝐚≠0}|²)^{1/2} ≤ C (|□_{m+1}|⁻¹ ∫_{𝒞_*(□_{m+1})} |∇u 1_{𝐚≠0}|^{s' 2_*})^{1/(s' 2_*)}`

with `2_* = 2d/(d+2)`. The proof combines the Caccioppoli inequality (Lemma 3.5), the Sobolev
inequality on the cluster (Proposition 3.4 with `s = 2`) and Hölder's inequality.

Here the Sobolev inequality is the hypothesis `ClusterSobolevTwo`: its mean-zero form, written with
the cell size `size x` of the partition cube containing `x` (the sum over partition cubes
`∑_{□'} size(□')^{2d} ∫_{□' ∩ 𝒞_*} |∇w|^{2_*}` is the sum over points of `size(x)^{2d} |∇w|^{2_*}(x)`).
The theorem `reverse_holder_of_sobolev` is stated for a finite set `U` (the cluster of the larger
cube) and `V ⊆ U` (the cluster of the smaller cube) at sup-norm distance at least `r` from the points
of `U` with an open edge leaving `U`, and with the volumes `N` and `N'` of the two cubes related by
`N^{2/2_*} ≤ K N' r²`; `triadic_volume_relation` checks this relation for `N = 3^{(m+1)d}`,
`N' = 3^{md}`, `r = 3^m` and `K = 3^{d+2}`. Hölder's inequality is applied point by point, which
makes Jensen's inequality on the partition cubes unnecessary.
-/

namespace Rigidity.Proofs.Cluster

open LatticeProb.Percolation
open scoped BigOperators Classical

variable {d : ℕ}

/-- The lower Sobolev exponent `2_* = 2d/(d+2)` of `2` in dimension `d`. -/
noncomputable def lowerSobolevTwo (d : ℕ) : ℝ := 2 * d / (d + 2)

theorem lowerSobolevTwo_pos (hd : 0 < d) : 0 < lowerSobolevTwo d := by
  unfold lowerSobolevTwo
  have : (0 : ℝ) < d := by exact_mod_cast hd
  positivity

theorem two_div_lowerSobolevTwo (hd : 0 < d) : 2 / lowerSobolevTwo d = ((d : ℝ) + 2) / d := by
  unfold lowerSobolevTwo
  have h1 : (d : ℝ) ≠ 0 := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    exact this.ne'
  have h2 : (d : ℝ) + 2 ≠ 0 := by positivity
  field_simp

/-- **The Sobolev inequality on a cluster for mean-zero functions**, the hypothesis of
Armstrong–Dario, Proposition 3.4, with `s = 2` and the alternative `∫_{𝒞_*} w = 0`: every `w` with
`∑_{x ∈ U} w x = 0` satisfies
`∑_{x ∈ U} w(x)² ≤ C (∑_{x ∈ U} size(x)^{2d} |∇w 1_{𝐚≠0}|^{2_*}(x))^{2/2_*}`,
where `|∇w 1_{𝐚≠0}|(x)² = clusterGradSq ω U w x` and `size x` is the size of the partition cube
containing `x`. -/
def ClusterSobolevTwo (ω : Configuration d) (U : Finset (Vertex d)) (size : Vertex d → ℝ)
    (C : ℝ) : Prop :=
  ∀ w : Vertex d → ℝ, ∑ x ∈ U, w x = 0 →
    ∑ x ∈ U, w x ^ 2 ≤
      C * (∑ x ∈ U, size x ^ (2 * (d : ℝ)) *
        clusterGradSq ω U w x ^ (lowerSobolevTwo d / 2)) ^ (2 / lowerSobolevTwo d)

theorem clusterGradSq_nonneg (ω : Configuration d) (U : Finset (Vertex d)) (u : Vertex d → ℝ)
    (x : Vertex d) : 0 ≤ clusterGradSq ω U u x := by
  unfold clusterGradSq
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun y _ => sq_nonneg _)

theorem clusterGradSq_sub_const (ω : Configuration d) (U : Finset (Vertex d))
    (u : Vertex d → ℝ) (a : ℝ) (x : Vertex d) :
    clusterGradSq ω U (fun y => u y - a) x = clusterGradSq ω U u x := by
  unfold clusterGradSq
  congr 1
  exact Finset.sum_congr rfl fun y _ => by ring

theorem openLaplacian_sub_const (ω : Configuration d) (u : Vertex d → ℝ) (a : ℝ)
    (x : Vertex d) : openLaplacian ω (fun y => u y - a) x = openLaplacian ω u x := by
  unfold openLaplacian
  exact Finset.sum_congr rfl fun y _ => by ring

/-- **Reverse Hölder inequality** (Armstrong–Dario, Lemma 3.6, deterministic part). Let `V ⊆ U`
be finite sets of lattice points, every point of `U` with an open edge leaving `U` at sup-norm
distance at least `r > 0` from `V`, and let `u` be harmonic for the open edges at the points of `U`
all of whose open edges stay in `U`. Assume the Sobolev inequality `ClusterSobolevTwo ω U size C_S`,
the moment bound `∑_{x ∈ U} size(x)^{2ds} ≤ C_G N` with `s` and `t` Hölder conjugate, and the volume
relation `N^{2/2_*} ≤ K N' r²`. Then
`N'⁻¹ ∑_{x ∈ V} |∇u|²(x) ≤ 8d C_S C_G^{2/(s 2_*)} K (N⁻¹ ∑_{x ∈ U} |∇u|^{t 2_*}(x))^{2/(t 2_*)}`,
with `|∇u|² = clusterGradSq ω U u`. -/
theorem reverse_holder_of_sobolev (ω : Configuration d) (hd : 0 < d) (U V : Finset (Vertex d))
    (hVU : V ⊆ U) {r : ℝ} (hr : 0 < r)
    (hdist : ∀ x ∈ V, ∀ z ∈ U, (∃ y, (openGraph ω).Adj z y ∧ y ∉ U) → r ≤ supDist x z)
    (size : Vertex d → ℝ) (hsize : ∀ x, 0 ≤ size x) {CS CG s t N N' K : ℝ}
    (hCS : 0 ≤ CS) (hCG : 0 ≤ CG) (hst : s.HolderConjugate t) (hN : 0 < N) (hN' : 0 < N')
    (hSob : ClusterSobolevTwo ω U size CS)
    (hgood : ∑ x ∈ U, size x ^ (2 * (d : ℝ) * s) ≤ CG * N)
    (hvol : N ^ (2 / lowerSobolevTwo d) ≤ K * N' * r ^ 2) (u : Vertex d → ℝ)
    (hu : ∀ x ∈ U, (∀ y, (openGraph ω).Adj x y → y ∈ U) → openLaplacian ω u x = 0) :
    (1 / N') * ∑ x ∈ V, clusterGradSq ω U u x ≤
      8 * d * CS * CG ^ (2 / (s * lowerSobolevTwo d)) * K *
        ((1 / N) * ∑ x ∈ U, clusterGradSq ω U u x ^ (t * lowerSobolevTwo d / 2)) ^
          (2 / (t * lowerSobolevTwo d)) := by
  set q := lowerSobolevTwo d with hqdef
  have hq : 0 < q := lowerSobolevTwo_pos hd
  have hs := hst.pos
  have ht := hst.symm.pos
  set a : ℝ := (∑ x ∈ U, u x) / U.card with ha
  set w : Vertex d → ℝ := fun y => u y - a with hw
  have hw0 : ∑ x ∈ U, w x = 0 := by
    simp only [hw, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    rcases Nat.eq_zero_or_pos U.card with h0 | h0
    · rw [Finset.card_eq_zero.mp h0]
      simp
    · rw [ha, mul_div_cancel₀ _ (by exact_mod_cast h0.ne')]
      ring
  have hgw : ∀ x, clusterGradSq ω U w x = clusterGradSq ω U u x :=
    fun x => clusterGradSq_sub_const ω U u a x
  have hcac := caccioppoli_cluster ω U V hVU hr hdist w fun x hx hall => by
    rw [hw, openLaplacian_sub_const]
    exact hu x hx hall
  simp only [hgw] at hcac
  have hcac' : ∑ x ∈ V, clusterGradSq ω U u x ≤ 8 * d / r ^ 2 * ∑ x ∈ U, w x ^ 2 :=
    hcac.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _) fun x _ _ => sq_nonneg _) (by positivity))
  have hsob := hSob w hw0
  simp only [hgw] at hsob
  -- Hölder's inequality, point by point
  set g : Vertex d → ℝ := fun x => clusterGradSq ω U u x ^ (q / 2) with hg
  set X : ℝ := ∑ x ∈ U, size x ^ (2 * (d : ℝ)) * g x with hX
  set Y : ℝ := ∑ x ∈ U, clusterGradSq ω U u x ^ (t * q / 2) with hY
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun x _ =>
    mul_nonneg (Real.rpow_nonneg (hsize x) _) (Real.rpow_nonneg (clusterGradSq_nonneg ω U u x) _)
  have hY0 : 0 ≤ Y := Finset.sum_nonneg fun x _ =>
    Real.rpow_nonneg (clusterGradSq_nonneg ω U u x) _
  have hHold : X ≤ (CG * N) ^ (1 / s) * Y ^ (1 / t) := by
    have h1 := Real.inner_le_Lp_mul_Lq_of_nonneg U hst
      (f := fun x => size x ^ (2 * (d : ℝ))) (g := g)
      (fun x _ => Real.rpow_nonneg (hsize x) _)
      (fun x _ => Real.rpow_nonneg (clusterGradSq_nonneg ω U u x) _)
    have h2 : ∑ x ∈ U, (size x ^ (2 * (d : ℝ))) ^ s = ∑ x ∈ U, size x ^ (2 * (d : ℝ) * s) :=
      Finset.sum_congr rfl fun x _ => (Real.rpow_mul (hsize x) _ _).symm
    have h3 : ∑ x ∈ U, g x ^ t = Y := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [hg, ← Real.rpow_mul (clusterGradSq_nonneg ω U u x)]
      congr 1
      ring
    rw [h2, h3] at h1
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hY0 _))
    exact Real.rpow_le_rpow (Finset.sum_nonneg fun x _ => Real.rpow_nonneg (hsize x) _) hgood
      (by positivity)
  have hHoldPow : X ^ (2 / q) ≤
      CG ^ (2 / (s * q)) * N ^ (2 / (s * q)) * Y ^ (2 / (t * q)) := by
    have h1 := Real.rpow_le_rpow hX0 hHold (by positivity : (0 : ℝ) ≤ 2 / q)
    rw [Real.mul_rpow (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg hY0 _),
      ← Real.rpow_mul (by positivity), ← Real.rpow_mul hY0,
      Real.mul_rpow hCG hN.le] at h1
    have e1 : 1 / s * (2 / q) = 2 / (s * q) := by ring
    have e2 : 1 / t * (2 / q) = 2 / (t * q) := by ring
    rw [e1, e2] at h1
    exact h1
  -- assembling
  set E : ℝ := N ^ (2 / (s * q)) with hE
  set F : ℝ := N ^ (2 / (t * q)) with hF
  have hFpos : 0 < F := Real.rpow_pos_of_pos hN _
  have hEF : E * F ≤ K * N' * r ^ 2 := by
    rw [hE, hF, ← Real.rpow_add hN]
    have hsum : 2 / (s * q) + 2 / (t * q) = 2 / q := by
      have h1 := hst.inv_add_inv_eq_one
      calc 2 / (s * q) + 2 / (t * q) = 2 / q * (s⁻¹ + t⁻¹) := by
            field_simp
        _ = 2 / q := by rw [h1, mul_one]
    rw [hsum]
    exact hvol
  set P : ℝ := 8 * d * CS * CG ^ (2 / (s * q)) with hP
  have hP0 : 0 ≤ P := by positivity
  have hZ0 : 0 ≤ Y ^ (2 / (t * q)) := Real.rpow_nonneg hY0 _
  have hV : ∑ x ∈ V, clusterGradSq ω U u x ≤ P * (E * Y ^ (2 / (t * q))) / r ^ 2 := by
    have h1 : ∑ x ∈ V, clusterGradSq ω U u x ≤ 8 * d / r ^ 2 * (CS * X ^ (2 / q)) :=
      hcac'.trans (mul_le_mul_of_nonneg_left hsob (by positivity))
    have h2 : 8 * d / r ^ 2 * (CS * X ^ (2 / q)) ≤
        8 * d / r ^ 2 * (CS * (CG ^ (2 / (s * q)) * E * Y ^ (2 / (t * q)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hHoldPow hCS) (by positivity)
    refine (h1.trans h2).trans_eq ?_
    rw [hP]
    ring
  have hRHS : ((1 / N) * Y) ^ (2 / (t * q)) = F⁻¹ * Y ^ (2 / (t * q)) := by
    rw [Real.mul_rpow (by positivity) hY0, one_div, Real.inv_rpow hN.le]
  rw [hRHS]
  have hkey : E / (N' * r ^ 2) ≤ K * F⁻¹ := by
    rw [div_le_iff₀ (by positivity)]
    calc E = E * F * F⁻¹ := by field_simp
      _ ≤ K * N' * r ^ 2 * F⁻¹ := mul_le_mul_of_nonneg_right hEF (inv_nonneg.mpr hFpos.le)
      _ = K * F⁻¹ * (N' * r ^ 2) := by ring
  calc (1 / N') * ∑ x ∈ V, clusterGradSq ω U u x
      ≤ (1 / N') * (P * (E * Y ^ (2 / (t * q))) / r ^ 2) :=
        mul_le_mul_of_nonneg_left hV (by positivity)
    _ = P * Y ^ (2 / (t * q)) * (E / (N' * r ^ 2)) := by
        field_simp
    _ ≤ P * Y ^ (2 / (t * q)) * (K * F⁻¹) :=
        mul_le_mul_of_nonneg_left hkey (mul_nonneg hP0 hZ0)
    _ = P * K * (F⁻¹ * Y ^ (2 / (t * q))) := by ring

/-- The volume relation of `reverse_holder_of_sobolev` for triadic cubes: with `N = 3^{(m+1)d}`,
`N' = 3^{md}` and `r = 3^m`, `N^{2/2_*} = 3^{d+2} N' r²`. -/
theorem triadic_volume_relation (hd : 0 < d) (m : ℕ) :
    ((3 : ℝ) ^ ((m + 1) * d)) ^ (2 / lowerSobolevTwo d) =
      (3 : ℝ) ^ (d + 2) * (3 : ℝ) ^ (m * d) * ((3 : ℝ) ^ m) ^ 2 := by
  rw [two_div_lowerSobolevTwo hd, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  have hd' : (d : ℝ) ≠ 0 := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    exact this.ne'
  have h1 : (((m + 1) * d : ℕ) : ℝ) * (((d : ℝ) + 2) / d) = (((m + 1) * (d + 2) : ℕ) : ℝ) := by
    push_cast
    field_simp
  rw [h1, Real.rpow_natCast, ← pow_mul, ← pow_add, ← pow_add]
  congr 1
  ring

end Rigidity.Proofs.Cluster
