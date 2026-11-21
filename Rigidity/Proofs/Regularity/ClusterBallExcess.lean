import LatticeProb.Prob.Percolation.LatticeClusterL2Triangle
import Rigidity.Proofs.Regularity.SinglePolynomial

/-!
# Cluster balls as a family of ball seminorms

The normalized `L²` norm `componentBallL2 C z r` on the intersection of an open cluster `C` with
the Euclidean ball `B_r(z)` is an additive group seminorm on the functions on `C`
(`componentBallSeminorm`). This file proves the two properties of
`Rigidity.Proofs.Regularity.BallExcess` that the iteration of Armstrong–Dario, Lemma 7.2
(arXiv:1609.09431v2), asks of the norms on balls and of the affine functions, from geometric
properties of the cluster which follow from its density in balls:

* `radiusMonotone_componentBallSeminorm`: if the cluster balls satisfy the volume comparison
  `#(C ∩ B_r) ≤ K (r / s) ^ d #(C ∩ B_s)` for `X ≤ s ≤ r ≤ R` (`ClusterBallVolumeComparison`),
  then `componentBallL2 C z s f ≤ √K (r / s) ^ (d / 2) componentBallL2 C z r f`;
* `polynomialComparison_componentBallSeminorm`: if every cluster ball `C ∩ B_ρ(z)`,
  `X ≤ ρ ≤ R`, has a fraction at least `δ` of its points in each of the two caps
  `±⟪p, x - z⟫ ≥ ‖p‖ ρ / 2` (`ClusterBallCapDensity`), then the excess of an affine function over
  the constants on the cluster balls scales like the radius, with constant `2 / √δ`.

For the Euclidean balls of `ℝ^d` both properties hold with `K = 1` and a dimensional `δ`; for the
infinite cluster they are consequences of the concentration of the density of the cluster in
cubes above a minimal scale.
-/

namespace Rigidity.Proofs.Regularity

open LatticeProb LatticeProb.Percolation

variable {d : ℕ} {ω : Configuration d}

/-- The normalized `L²` norm on a cluster ball as an additive group seminorm. -/
noncomputable def componentBallSeminorm (C : OpenComponent ω) (z : Vertex d) (r : ℝ) :
    AddGroupSeminorm (C → ℝ) where
  toFun := componentBallL2 C z r
  map_zero' := componentBallL2_zero C z r
  add_le' := componentBallL2_add_le C z r
  neg' u := by
    have := componentBallL2_smul C z r (-1) u
    rwa [neg_one_smul, abs_neg, abs_one, one_mul] at this

@[simp] theorem componentBallSeminorm_apply (C : OpenComponent ω) (z : Vertex d) (r : ℝ)
    (u : C → ℝ) : componentBallSeminorm C z r u = componentBallL2 C z r u :=
  rfl

/-- The volume comparison of cluster balls between the radii `X ≤ s ≤ r ≤ R`. -/
def ClusterBallVolumeComparison (C : OpenComponent ω) (z : Vertex d) (X R K : ℝ) : Prop :=
  ∀ s r : ℝ, X ≤ s → s ≤ r → r ≤ R →
    ((componentEuclideanBall C z r).card : ℝ) ≤
      K * (r / s) ^ d * ((componentEuclideanBall C z s).card : ℝ)

theorem componentEuclideanBall_mono (C : OpenComponent ω) (z : Vertex d) {s r : ℝ}
    (hsr : s ≤ r) : componentEuclideanBall C z s ⊆ componentEuclideanBall C z r := by
  intro x hx
  rw [mem_componentEuclideanBall] at hx ⊢
  exact hx.trans_le hsr

/-- **Volume factor for cluster balls.** -/
theorem radiusMonotone_componentBallSeminorm (C : OpenComponent ω) (z : Vertex d) {X R K : ℝ}
    (hX : 0 < X) (hK : 0 ≤ K) (hvol : ClusterBallVolumeComparison C z X R K) :
    RadiusMonotone (componentBallSeminorm C z) X R (Real.sqrt K) ((d : ℝ) / 2) := by
  intro f s r hXs hsr hrR
  have hs0 : 0 < s := hX.trans_le hXs
  have hr0 : 0 < r := hs0.trans_le hsr
  simp only [componentBallSeminorm_apply, componentBallL2]
  set Bs := componentEuclideanBall C z s
  set Br := componentEuclideanBall C z r
  have hsub : Bs ⊆ Br := componentEuclideanBall_mono C z hsr
  have hSs : ∑ x ∈ Bs, f x ^ 2 ≤ ∑ x ∈ Br, f x ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _
  have hSr : 0 ≤ ∑ x ∈ Br, f x ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rcases Nat.eq_zero_or_pos Bs.card with hcs | hcs
  · rw [hcs, Nat.cast_zero, div_zero, Real.sqrt_zero]
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
      (Real.rpow_nonneg (div_nonneg hr0.le hs0.le) _)) (Real.sqrt_nonneg _)
  have hcs' : (0 : ℝ) < Bs.card := by exact_mod_cast hcs
  have hcr' : (0 : ℝ) < Br.card := hcs'.trans_le (by exact_mod_cast Finset.card_le_card hsub)
  have hv := hvol s r hXs hsr hrR
  have hpow : ((r / s) ^ ((d : ℝ) / 2)) ^ 2 = (r / s) ^ d := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (div_nonneg hr0.le hs0.le)]
    norm_num [← Real.rpow_natCast]
  have hrs0 : 0 ≤ (r / s) ^ ((d : ℝ) / 2) := Real.rpow_nonneg (div_nonneg hr0.le hs0.le) _
  rw [← Real.sqrt_sq hrs0, ← Real.sqrt_mul hK, ← Real.sqrt_mul (mul_nonneg hK (sq_nonneg _))]
  apply Real.sqrt_le_sqrt
  rw [hpow, div_le_iff₀ hcs']
  calc ∑ x ∈ Bs, f x ^ 2 ≤ ∑ x ∈ Br, f x ^ 2 := hSs
    _ = (∑ x ∈ Br, f x ^ 2) / Br.card * Br.card := by field_simp
    _ ≤ (∑ x ∈ Br, f x ^ 2) / Br.card * (K * (r / s) ^ d * Bs.card) :=
        mul_le_mul_of_nonneg_left hv (div_nonneg hSr hcr'.le)
    _ = K * (r / s) ^ d * ((∑ x ∈ Br, f x ^ 2) / Br.card) * Bs.card := by ring

/-- The constant functions on a cluster. -/
def clusterConstants (C : OpenComponent ω) : AddSubgroup (C → ℝ) where
  carrier := {f | ∃ c : ℝ, ∀ x, f x = c}
  add_mem' := by
    rintro f g ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a + b, fun x => by simp [ha, hb]⟩
  zero_mem' := ⟨0, fun _ => rfl⟩
  neg_mem' := by
    rintro f ⟨a, ha⟩
    exact ⟨-a, fun x => by simp [ha]⟩

/-- The restrictions to a cluster of the affine functions `x ↦ a + ⟪p, x⟫` of `ℝ^d`. -/
def clusterAffine (C : OpenComponent ω) : AddSubgroup (C → ℝ) where
  carrier := {f | ∃ (a : ℝ) (p : EuclideanSpace ℝ (Fin d)),
    ∀ x, f x = a + inner ℝ p (latticeEuclideanEmbedding x.val)}
  add_mem' := by
    rintro f g ⟨a, p, ha⟩ ⟨b, q, hb⟩
    refine ⟨a + b, p + q, fun x => ?_⟩
    simp only [Pi.add_apply, ha, hb, inner_add_left]
    ring
  zero_mem' := ⟨0, 0, fun _ => by simp⟩
  neg_mem' := by
    rintro f ⟨a, p, ha⟩
    refine ⟨-a, -p, fun x => ?_⟩
    simp only [Pi.neg_apply, ha, inner_neg_left]
    ring

theorem clusterConstants_le_clusterAffine (C : OpenComponent ω) :
    clusterConstants C ≤ clusterAffine C := by
  rintro f ⟨c, hc⟩
  exact ⟨c, 0, fun x => by simp [hc]⟩

/-- Every cluster ball `C ∩ B_ρ(z)`, `X ≤ ρ ≤ R`, has at least the fraction `δ` of its points in
each of the caps `⟪p, x - z⟫ ≥ ‖p‖ ρ / 2` and `⟪p, x - z⟫ ≤ -‖p‖ ρ / 2`, and is nonempty. -/
def ClusterBallCapDensity (C : OpenComponent ω) (z : Vertex d) (X R δ : ℝ) : Prop :=
  ∀ ρ : ℝ, X ≤ ρ → ρ ≤ R → 0 < (componentEuclideanBall C z ρ).card ∧
    ∀ p : EuclideanSpace ℝ (Fin d),
    δ * (componentEuclideanBall C z ρ).card ≤
        ((componentEuclideanBall C z ρ).filter fun x =>
          ‖p‖ * ρ / 2 ≤ inner ℝ p (latticeEuclideanEmbedding x.val -
            latticeEuclideanEmbedding z)).card ∧
      δ * (componentEuclideanBall C z ρ).card ≤
        ((componentEuclideanBall C z ρ).filter fun x =>
          inner ℝ p (latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding z) ≤
            -(‖p‖ * ρ / 2)).card

/-- A pointwise bound on a cluster ball bounds the normalized `L²` norm. -/
theorem componentBallL2_le_of_abs_le (C : OpenComponent ω) (z : Vertex d) (r : ℝ) {g : C → ℝ}
    {M : ℝ} (hM : 0 ≤ M) (h : ∀ x ∈ componentEuclideanBall C z r, |g x| ≤ M) :
    componentBallL2 C z r g ≤ M := by
  unfold componentBallL2
  rcases Nat.eq_zero_or_pos (componentEuclideanBall C z r).card with h0 | h0
  · rw [h0, Nat.cast_zero, div_zero, Real.sqrt_zero]; exact hM
  refine Real.sqrt_le_iff.2 ⟨hM, ?_⟩
  rw [div_le_iff₀ (by exact_mod_cast h0)]
  calc ∑ x ∈ componentEuclideanBall C z r, g x ^ 2 ≤
        ∑ _x ∈ componentEuclideanBall C z r, M ^ 2 :=
        Finset.sum_le_sum fun x hx => by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h x hx) 2
    _ = M ^ 2 * (componentEuclideanBall C z r).card := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- A lower bound on a subset carrying the fraction `δ` of a cluster ball bounds the normalized
`L²` norm from below. -/
theorem le_componentBallL2_of_subset (C : OpenComponent ω) (z : Vertex d) (r : ℝ) {g : C → ℝ}
    {m δ : ℝ} (hm : 0 ≤ m) (hδ : 0 ≤ δ) (hcard : 0 < (componentEuclideanBall C z r).card)
    {S : Finset C} (hS : S ⊆ componentEuclideanBall C z r) (hSm : ∀ x ∈ S, m ≤ |g x|)
    (hSδ : δ * (componentEuclideanBall C z r).card ≤ S.card) :
    Real.sqrt δ * m ≤ componentBallL2 C z r g := by
  unfold componentBallL2
  have hc : (0 : ℝ) < (componentEuclideanBall C z r).card := by exact_mod_cast hcard
  rw [← Real.sqrt_sq hm, ← Real.sqrt_mul hδ]
  apply Real.sqrt_le_sqrt
  rw [le_div_iff₀ hc]
  calc δ * m ^ 2 * (componentEuclideanBall C z r).card =
        δ * (componentEuclideanBall C z r).card * m ^ 2 := by ring
    _ ≤ S.card * m ^ 2 := mul_le_mul_of_nonneg_right hSδ (sq_nonneg _)
    _ = ∑ _x ∈ S, m ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ x ∈ S, g x ^ 2 := Finset.sum_le_sum fun x hx => by
        rw [← sq_abs (g x)]; exact pow_le_pow_left₀ hm (hSm x hx) 2
    _ ≤ ∑ x ∈ componentEuclideanBall C z r, g x ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hS fun _ _ _ => sq_nonneg _

/-- The excess over the constants of the affine function `a + ⟪p, x⟫` on the cluster ball of
radius `ρ > 0` is at most `‖p‖ ρ`. -/
theorem ballExcess_clusterAffine_le (C : OpenComponent ω) (z : Vertex d) {ρ : ℝ} (hρ : 0 ≤ ρ)
    {w : C → ℝ} {a : ℝ} {p : EuclideanSpace ℝ (Fin d)}
    (hw : ∀ x, w x = a + inner ℝ p (latticeEuclideanEmbedding x.val)) :
    ballExcess (componentBallSeminorm C z) (clusterConstants C) ρ w ≤ ‖p‖ * ρ := by
  have hmem : (fun _ : C => a + inner ℝ p (latticeEuclideanEmbedding z)) ∈ clusterConstants C :=
    ⟨_, fun _ => rfl⟩
  refine (ballExcess_le _ _ hmem).trans ?_
  rw [componentBallSeminorm_apply]
  apply componentBallL2_le_of_abs_le C z ρ (mul_nonneg (norm_nonneg _) hρ)
  intro x hx
  rw [mem_componentEuclideanBall, dist_eq_norm] at hx
  have : (w - fun _ : C => a + inner ℝ p (latticeEuclideanEmbedding z)) x =
      inner ℝ p (latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding z) := by
    simp only [Pi.sub_apply, hw, inner_sub_right]; ring
  rw [this]
  exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hx.le (norm_nonneg _))

/-- Under `ClusterBallCapDensity`, the excess over the constants of the affine function
`a + ⟪p, x⟫` on the cluster ball of radius `ρ ∈ [X, R]` is at least `√δ ‖p‖ ρ / 2`. -/
theorem le_ballExcess_clusterAffine (C : OpenComponent ω) (z : Vertex d) {X R δ ρ : ℝ}
    (hδ : 0 ≤ δ) (hcap : ClusterBallCapDensity C z X R δ) (hXρ : X ≤ ρ) (hρR : ρ ≤ R)
    (hρ : 0 ≤ ρ) {w : C → ℝ} {a : ℝ} {p : EuclideanSpace ℝ (Fin d)}
    (hw : ∀ x, w x = a + inner ℝ p (latticeEuclideanEmbedding x.val)) :
    Real.sqrt δ * (‖p‖ * ρ / 2) ≤
      ballExcess (componentBallSeminorm C z) (clusterConstants C) ρ w := by
  obtain ⟨hcard, hcaps⟩ := hcap ρ hXρ hρR
  obtain ⟨hplus, hminus⟩ := hcaps p
  have hm : 0 ≤ ‖p‖ * ρ / 2 := by positivity
  apply le_ballExcess
  rintro g ⟨c, hc⟩
  rw [componentBallSeminorm_apply]
  set t := c - a - inner ℝ p (latticeEuclideanEmbedding z) with ht
  have hval : ∀ x : C, (w - g) x =
      inner ℝ p (latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding z) - t := by
    intro x
    simp only [Pi.sub_apply, hw, hc, inner_sub_right, ht]; ring
  rcases le_or_gt t 0 with htn | htp
  · refine le_componentBallL2_of_subset C z ρ hm hδ hcard (Finset.filter_subset _ _) ?_ hplus
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [hval]
    exact le_abs.2 (Or.inl (by linarith [hx.2]))
  · refine le_componentBallL2_of_subset C z ρ hm hδ hcard (Finset.filter_subset _ _) ?_ hminus
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [hval]
    exact le_abs.2 (Or.inr (by linarith [hx.2]))

/-- **Polynomial comparison for affine functions on cluster balls**, from
`ClusterBallCapDensity` with `δ > 0`: `PolynomialComparison` holds for the constants inside the
affine functions with degree `1` and constant `2 / √δ`. -/
theorem polynomialComparison_componentBallSeminorm (C : OpenComponent ω) (z : Vertex d)
    {X R δ : ℝ} (hX : 0 < X) (hδ : 0 < δ) (hcap : ClusterBallCapDensity C z X R δ) :
    PolynomialComparison (componentBallSeminorm C z) (clusterConstants C) (clusterAffine C) 1 X R
      (2 / Real.sqrt δ) := by
  rintro w ⟨a, p, hw⟩ ρ ρ' hXρ hρρ' hρ'R
  have hρ0 : 0 < ρ := hX.trans_le hXρ
  have hρ'0 : 0 < ρ' := hρ0.trans_le hρρ'
  have hsδ : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hup := ballExcess_clusterAffine_le C z hρ0.le hw
  have hlow := le_ballExcess_clusterAffine C z hδ.le hcap (hXρ.trans hρρ') hρ'R
    hρ'0.le hw
  rw [pow_one]
  calc ballExcess (componentBallSeminorm C z) (clusterConstants C) ρ w ≤ ‖p‖ * ρ := hup
    _ = 2 / Real.sqrt δ * (ρ / ρ') * (Real.sqrt δ * (‖p‖ * ρ' / 2)) := by
        field_simp
    _ ≤ 2 / Real.sqrt δ * (ρ / ρ') *
        ballExcess (componentBallSeminorm C z) (clusterConstants C) ρ' w :=
        mul_le_mul_of_nonneg_left hlow (by positivity)

/-- On nonempty cluster balls the normalized norm of a constant is its absolute value, so the
constants satisfy `PolynomialGrowth` with `k = 0` and constant `1`. -/
theorem polynomialGrowth_clusterConstants (C : OpenComponent ω) (z : Vertex d) {X R : ℝ}
    (hne : ∀ ρ : ℝ, X ≤ ρ → ρ ≤ R → (componentEuclideanBall C z ρ).Nonempty) :
    PolynomialGrowth (componentBallSeminorm C z) (clusterConstants C) 0 X R 1 := by
  rintro w ⟨c, hc⟩ ρ r hXρ hρr hrR
  have hw : w = fun _ => c := funext hc
  rw [hw, componentBallSeminorm_apply, componentBallSeminorm_apply,
    componentBallL2_const C z r c (hne r (hXρ.trans hρr) hrR),
    componentBallL2_const C z ρ c (hne ρ hXρ (hρr.trans hrR)), pow_zero, one_mul, one_mul]

/-- Under `ClusterBallCapDensity` with `δ > 0`, the affine functions on the cluster satisfy
`PolynomialGrowth` with `k = 1` and constant `2 / √δ`: on `B_r(z)` the function
`c + ⟪p, x - z⟫` is at most `|c| + ‖p‖ r`, and its normalized norm on `B_ρ(z)` is at least
`√δ (|c| + ‖p‖ ρ) / 2`. -/
theorem polynomialGrowth_clusterAffine (C : OpenComponent ω) (z : Vertex d) {X R δ : ℝ}
    (hX : 0 < X) (hδ : 0 < δ) (hcap : ClusterBallCapDensity C z X R δ) :
    PolynomialGrowth (componentBallSeminorm C z) (clusterAffine C) 1 X R (2 / Real.sqrt δ) := by
  rintro w ⟨a, p, hw⟩ ρ r hXρ hρr hrR
  have hρ0 : 0 < ρ := hX.trans_le hXρ
  have hr0 : 0 < r := hρ0.trans_le hρr
  have hsδ : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  set c := a + inner ℝ p (latticeEuclideanEmbedding z) with hc
  have hwc : ∀ x : C, w x = c + inner ℝ p (latticeEuclideanEmbedding x.val -
      latticeEuclideanEmbedding z) := by
    intro x; rw [hw, hc, inner_sub_right]; ring
  have hup : componentBallL2 C z r w ≤ |c| + ‖p‖ * r := by
    apply componentBallL2_le_of_abs_le C z r (by positivity)
    intro x hx
    rw [mem_componentEuclideanBall, dist_eq_norm] at hx
    rw [hwc]
    calc |c + inner ℝ p (latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding z)|
        ≤ |c| + |inner ℝ p (latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding z)| :=
          abs_add_le _ _
      _ ≤ |c| + ‖p‖ * r := by
          gcongr
          exact (abs_real_inner_le_norm _ _).trans
            (mul_le_mul_of_nonneg_left hx.le (norm_nonneg _))
  obtain ⟨hcard, hcaps⟩ := hcap ρ hXρ (hρr.trans hrR)
  obtain ⟨hplus, hminus⟩ := hcaps p
  have hm : 0 ≤ (|c| + ‖p‖ * ρ) / 2 := by positivity
  have hlow : Real.sqrt δ * ((|c| + ‖p‖ * ρ) / 2) ≤ componentBallL2 C z ρ w := by
    rcases le_or_gt 0 c with hc0 | hc0
    · refine le_componentBallL2_of_subset C z ρ hm hδ.le hcard (Finset.filter_subset _ _) ?_
        hplus
      intro x hx
      rw [Finset.mem_filter] at hx
      rw [hwc, abs_of_nonneg hc0]
      refine le_abs.2 (Or.inl ?_)
      have := norm_nonneg p
      nlinarith [hx.2, mul_nonneg (norm_nonneg p) hρ0.le]
    · refine le_componentBallL2_of_subset C z ρ hm hδ.le hcard (Finset.filter_subset _ _) ?_
        hminus
      intro x hx
      rw [Finset.mem_filter] at hx
      rw [hwc, abs_of_neg hc0]
      refine le_abs.2 (Or.inr ?_)
      nlinarith [hx.2, mul_nonneg (norm_nonneg p) hρ0.le]
  rw [componentBallSeminorm_apply, componentBallSeminorm_apply, pow_one]
  have hratio : 1 ≤ r / ρ := (one_le_div hρ0).2 hρr
  calc componentBallL2 C z r w ≤ |c| + ‖p‖ * r := hup
    _ ≤ r / ρ * (|c| + ‖p‖ * ρ) := by
        have e : r / ρ * (‖p‖ * ρ) = ‖p‖ * r := by field_simp
        nlinarith [abs_nonneg c]
    _ = 2 / Real.sqrt δ * (r / ρ) * (Real.sqrt δ * ((|c| + ‖p‖ * ρ) / 2)) := by
        field_simp
    _ ≤ 2 / Real.sqrt δ * (r / ρ) * componentBallL2 C z ρ w :=
        mul_le_mul_of_nonneg_left hlow (by positivity)

end Rigidity.Proofs.Regularity
