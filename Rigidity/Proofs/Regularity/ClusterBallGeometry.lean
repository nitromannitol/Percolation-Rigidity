import Rigidity.External.ClusterDensity
import Rigidity.Proofs.Regularity.ClusterBallExcess

/-!
# Volume comparison and cap density of cluster balls from the density in cubes

The cluster-ball properties `ClusterBallVolumeComparison` and `ClusterBallCapDensity` used by the
iteration of Armstrong–Dario, Lemma 7.2 (arXiv:1609.09431v2), on cluster balls follow from a lower
bound on the density of the cluster in the triadic cubes `□_m(3^m k)` (`triadicCube`) of size
`3^m ≥ ℓ` inside the ball `B_{Λ 3^m}(z)`, `Λ = 24 √d` (`ClusterCubeDensity`): every cluster ball
`C ∩ B_s(z)`, `s ≥ 6 √d max ℓ 1`, contains a cube of size comparable to `s` near `z`, and every cap
`C ∩ B_ρ(z) ∩ {±⟪p, x - z⟫ ≥ ‖p‖ ρ / 2}`, `ρ ≥ 24 √d max ℓ 1`, contains a cube of size
comparable to `ρ` near `z ± (3ρ / 4) p / ‖p‖`, while a ball of radius `r ≥ 1` has at most
`(2 r + 3) ^ d` lattice points (`card_componentEuclideanBall_le`).

For the infinite cluster of supercritical bond percolation, the cube density with `κ = θ(p) / 2`
above a minimal scale is the consequence of the concentration of the density in triadic cubes
(Dario–Gu, Proposition A.1, `Rigidity.External.ClusterDensityConcentrationInput`).
-/

namespace Rigidity.Proofs.Regularity

open LatticeProb LatticeProb.Percolation Rigidity.External

variable {d : ℕ} {ω : Configuration d}

theorem abs_sub_le_dist_latticeEuclideanEmbedding (y z : Vertex d) (i : Fin d) :
    |(y i : ℝ) - (z i : ℝ)| ≤ dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding z) := by
  have hi := PiLp.norm_apply_le (latticeEuclideanEmbedding y - latticeEuclideanEmbedding z) i
  change |(y i : ℝ) - (z i : ℝ)| ≤
    ‖latticeEuclideanEmbedding y - latticeEuclideanEmbedding z‖ at hi
  rwa [dist_eq_norm]

theorem dist_latticeEuclideanEmbedding_le {y : Vertex d} {w : EuclideanSpace ℝ (Fin d)} {a : ℝ}
    (ha : 0 ≤ a) (h : ∀ i, |(y i : ℝ) - w i| ≤ a) :
    dist (latticeEuclideanEmbedding y) w ≤ Real.sqrt d * a := by
  rw [EuclideanSpace.dist_eq]
  calc Real.sqrt (∑ i, dist (latticeEuclideanEmbedding y i) (w i) ^ 2)
      ≤ Real.sqrt (∑ _i : Fin d, a ^ 2) := by
        apply Real.sqrt_le_sqrt
        apply Finset.sum_le_sum
        intro i _
        have hy : latticeEuclideanEmbedding y i = (y i : ℝ) := rfl
        rw [Real.dist_eq, hy]
        exact pow_le_pow_left₀ (abs_nonneg _) (h i) 2
    _ = Real.sqrt d * a := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq ha]

/-- A cluster ball of radius `r ≥ 0` has at most `(2 r + 3) ^ d` vertices. -/
theorem card_componentEuclideanBall_le (C : OpenComponent ω) (z : Vertex d) {r : ℝ}
    (hr : 0 ≤ r) : ((componentEuclideanBall C z r).card : ℝ) ≤ (2 * r + 3) ^ d := by
  classical
  set box := Fintype.piFinset fun i : Fin d => Finset.Icc (z i - ⌈r⌉) (z i + ⌈r⌉)
  have hsub : (componentEuclideanBall C z r).map (Function.Embedding.subtype _) ⊆ box := by
    intro y hy
    rw [Finset.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [mem_componentEuclideanBall] at hx
    rw [Fintype.mem_piFinset]
    intro i
    have h1 := abs_sub_le_dist_latticeEuclideanEmbedding x.val z i
    have h2 : |(x.val i : ℝ) - (z i : ℝ)| ≤ (⌈r⌉ : ℝ) := (h1.trans hx.le).trans (Int.le_ceil r)
    obtain ⟨hl, hu⟩ := abs_le.1 h2
    rw [Finset.mem_Icc]
    constructor
    · exact_mod_cast (by linarith : (z i : ℝ) - (⌈r⌉ : ℝ) ≤ (x.val i : ℝ))
    · exact_mod_cast (by linarith : (x.val i : ℝ) ≤ (z i : ℝ) + (⌈r⌉ : ℝ))
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_map] at hcard
  have hIcc : ∀ i, ((Finset.Icc (z i - ⌈r⌉) (z i + ⌈r⌉)).card : ℝ) ≤ 2 * r + 3 := by
    intro i
    rw [Int.card_Icc]
    have h0 : 0 ≤ z i + ⌈r⌉ + 1 - (z i - ⌈r⌉) := by
      have := Int.ceil_nonneg hr
      linarith
    have hcast : (((z i + ⌈r⌉ + 1 - (z i - ⌈r⌉)).toNat : ℕ) : ℝ) =
        ((z i + ⌈r⌉ + 1 - (z i - ⌈r⌉) : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg h0
    rw [hcast]
    push_cast
    linarith [Int.ceil_lt_add_one r]
  have hbox : (box.card : ℝ) ≤ (2 * r + 3) ^ d := by
    rw [Fintype.card_piFinset, Nat.cast_prod]
    calc ∏ i, ((Finset.Icc (z i - ⌈r⌉) (z i + ⌈r⌉)).card : ℝ) ≤ ∏ _i : Fin d, (2 * r + 3) :=
          Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) fun i _ => hIcc i
      _ = (2 * r + 3) ^ d := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact (Nat.cast_le.2 hcard).trans hbox

/-- The vertices of the cluster ball `C ∩ B_R(z)` in the triadic cube `□_m(3^m k)`. -/
noncomputable def clusterCubePoints (C : OpenComponent ω) (z : Vertex d) (R : ℝ) (m : ℕ)
    (k : Vertex d) : Finset C :=
  (componentEuclideanBall C z R).filter fun x =>
    ∀ i, |((x.val i : ℤ) : ℝ) - 3 ^ m * (k i : ℝ)| < 3 ^ m / 2

/-- Every triadic cube of size `3^m ≥ ℓ` inside the ball `B_{Λ 3^m}(z)` carries at least
`κ 3^{d m}` vertices of the cluster `C`. -/
def ClusterCubeDensity (C : OpenComponent ω) (z : Vertex d) (Λ ℓ κ : ℝ) : Prop :=
  ∀ (m : ℕ) (k : Vertex d), ℓ ≤ 3 ^ m →
    (∀ y ∈ triadicCube d m k, dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding z) <
      Λ * 3 ^ m) →
    κ * 3 ^ (d * m) ≤ (clusterCubePoints C z (Λ * 3 ^ m) m k).card

/-- The cube density for the cubes inside `B_{Λ' 3^m}(z)` gives it for `Λ ≤ Λ'`. -/
theorem ClusterCubeDensity.of_le (C : OpenComponent ω) (z : Vertex d) {Λ Λ' ℓ κ : ℝ}
    (h : ClusterCubeDensity C z Λ' ℓ κ) (hΛ : Λ ≤ Λ') : ClusterCubeDensity C z Λ ℓ κ := by
  intro m k hm hk
  have h3 : (0 : ℝ) < 3 ^ m := by positivity
  have hk' : ∀ y ∈ triadicCube d m k,
      dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding z) < Λ' * 3 ^ m :=
    fun y hy => (hk y hy).trans_le (mul_le_mul_of_nonneg_right hΛ h3.le)
  have e : clusterCubePoints C z (Λ * 3 ^ m) m k = clusterCubePoints C z (Λ' * 3 ^ m) m k := by
    ext x
    simp only [clusterCubePoints, Finset.mem_filter, mem_componentEuclideanBall]
    exact ⟨fun hx => ⟨hk' x.val hx.2, hx.2⟩, fun hx => ⟨hk x.val hx.2, hx.2⟩⟩
  rw [e]
  exact h m k hm hk'

/-- The triadic cube of size `3^m` nearest to a point `w` lies within `√d 3^m` of `w`. -/
theorem dist_le_of_mem_triadicCube_round (m : ℕ) (w : EuclideanSpace ℝ (Fin d)) {y : Vertex d}
    (hy : ∀ i, |(y i : ℝ) - 3 ^ m * ((round (w i / 3 ^ m) : ℤ) : ℝ)| < 3 ^ m / 2) :
    dist (latticeEuclideanEmbedding y) w ≤ Real.sqrt d * 3 ^ m := by
  apply dist_latticeEuclideanEmbedding_le (by positivity)
  intro i
  have h3 : (0 : ℝ) < 3 ^ m := by positivity
  have h1 := abs_sub_round (w i / 3 ^ m)
  have h2 : |3 ^ m * ((round (w i / 3 ^ m) : ℤ) : ℝ) - w i| ≤ 3 ^ m / 2 := by
    have e : 3 ^ m * ((round (w i / 3 ^ m) : ℤ) : ℝ) - w i =
        -(3 ^ m * (w i / 3 ^ m - round (w i / 3 ^ m))) := by field_simp; ring
    rw [e, abs_neg, abs_mul, abs_of_pos h3]
    nlinarith
  calc |(y i : ℝ) - w i| ≤ |(y i : ℝ) - 3 ^ m * ((round (w i / 3 ^ m) : ℤ) : ℝ)| +
        |3 ^ m * ((round (w i / 3 ^ m) : ℤ) : ℝ) - w i| := abs_sub_le _ _ _
    _ ≤ 3 ^ m := by linarith [hy i]

/-- **A cube near `w`.** If the ball of radius `√d 3^m` around `w` lies in `B_ρ(z)`,
`ρ ≤ Λ 3^m`, and `3^m ≥ ℓ`, then at least `κ 3^{d m}` vertices of `C ∩ B_ρ(z)` lie within
`√d 3^m` of `w`. -/
theorem le_card_filter_of_clusterCubeDensity (C : OpenComponent ω) (z : Vertex d)
    {Λ ℓ κ ρ : ℝ} (hcube : ClusterCubeDensity C z Λ ℓ κ) {m : ℕ} (hℓ : ℓ ≤ 3 ^ m)
    {w : EuclideanSpace ℝ (Fin d)}
    (hw : dist w (latticeEuclideanEmbedding z) + Real.sqrt d * 3 ^ m < ρ)
    (hρR : ρ ≤ Λ * 3 ^ m)
    (P : C → Prop) [DecidablePred P]
    (hP : ∀ x : C, dist (latticeEuclideanEmbedding x.val) w ≤ Real.sqrt d * 3 ^ m → P x) :
    κ * 3 ^ (d * m) ≤ ((componentEuclideanBall C z ρ).filter P).card := by
  set k : Vertex d := fun i => round (w i / 3 ^ m) with hk
  have hin : ∀ y : Vertex d, (∀ i, |(y i : ℝ) - 3 ^ m * (k i : ℝ)| < 3 ^ m / 2) →
      dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding z) < ρ := by
    intro y hy
    have := dist_le_of_mem_triadicCube_round m w hy
    calc dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding z)
        ≤ dist (latticeEuclideanEmbedding y) w + dist w (latticeEuclideanEmbedding z) :=
          dist_triangle _ _ _
      _ < ρ := by linarith
  have h1 := hcube m k hℓ fun y hy => (hin y hy).trans_le hρR
  refine h1.trans (Nat.cast_le.2 (Finset.card_le_card ?_))
  intro x hx
  simp only [clusterCubePoints, Finset.mem_filter] at hx
  rw [Finset.mem_filter, mem_componentEuclideanBall]
  exact ⟨hin x.val hx.2, hP x (dist_le_of_mem_triadicCube_round m w hx.2)⟩

/-- **Volume comparison of cluster balls** from the density in cubes. -/
theorem clusterBallVolumeComparison_of_clusterCubeDensity (C : OpenComponent ω) (z : Vertex d)
    {ℓ κ : ℝ} (R : ℝ) (hd : 0 < d) (hκ : 0 < κ)
    (hcube : ClusterCubeDensity C z (24 * Real.sqrt d) ℓ κ) :
    ClusterBallVolumeComparison C z (6 * Real.sqrt d * max ℓ 1) R
      ((5 * (6 * Real.sqrt d)) ^ d / κ) := by
  classical
  intro s r hs hsr hrR
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 (Nat.cast_pos.2 hd)
  have hmax1 : 1 ≤ max ℓ 1 := le_max_right _ _
  have hs6 : 6 * Real.sqrt d ≤ s := by nlinarith
  have hsℓ : 6 * Real.sqrt d * ℓ ≤ s :=
    (mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)).trans hs
  have hs0 : 0 < s := by linarith
  have hsd1 : 1 ≤ Real.sqrt d := Real.one_le_sqrt.2 (Nat.one_le_cast.2 hd)
  have hs1 : 1 ≤ s := by linarith
  have hx : 1 ≤ s / (2 * Real.sqrt d) := by rw [le_div_iff₀ (by positivity)]; linarith
  obtain ⟨m, hm1, hm2⟩ := exists_nat_pow_near hx (by norm_num : (1 : ℝ) < 3)
  have h3m : s / (6 * Real.sqrt d) < 3 ^ m := by
    rw [pow_succ] at hm2
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ (by positivity)] at hm2
    linarith
  have hℓ : ℓ ≤ 3 ^ m := by
    refine le_trans ?_ h3m.le
    rw [le_div_iff₀ (by positivity)]; linarith
  have hw : dist (latticeEuclideanEmbedding z) (latticeEuclideanEmbedding z) +
      Real.sqrt d * 3 ^ m < s := by
    rw [dist_self, zero_add]
    rw [le_div_iff₀ (by positivity)] at hm1
    linarith
  have hs24 : s ≤ 24 * Real.sqrt d * 3 ^ m := by
    rw [pow_succ, div_lt_iff₀ (by positivity)] at hm2
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 3) m]
  have hcount := le_card_filter_of_clusterCubeDensity C z hcube hℓ hw hs24
    (fun _ => True) fun _ _ => trivial
  rw [Finset.filter_true] at hcount
  have hr1 : 1 ≤ r := hs1.trans hsr
  have h1 : ((componentEuclideanBall C z r).card : ℝ) ≤ (5 * r) ^ d :=
    (card_componentEuclideanBall_le C z (by linarith)).trans
      (pow_le_pow_left₀ (by linarith) (by linarith) d)
  have h2 : (5 * r) ^ d = (5 * (6 * Real.sqrt d)) ^ d * (r / s) ^ d *
      (s / (6 * Real.sqrt d)) ^ d := by
    rw [← mul_pow, ← mul_pow]
    congr 1
    field_simp
  have h3 : (s / (6 * Real.sqrt d)) ^ d ≤ (3 ^ m) ^ d :=
    pow_le_pow_left₀ (by positivity) h3m.le d
  have h4 : (3 : ℝ) ^ (d * m) = (3 ^ m) ^ d := by rw [show d * m = m * d from mul_comm d m, pow_mul]
  rw [h4] at hcount
  have hA : 0 ≤ (5 * (6 * Real.sqrt d)) ^ d * (r / s) ^ d := by positivity
  calc ((componentEuclideanBall C z r).card : ℝ)
      ≤ (5 * (6 * Real.sqrt d)) ^ d * (r / s) ^ d * (3 ^ m) ^ d := by
        rw [h2] at h1
        exact h1.trans (mul_le_mul_of_nonneg_left h3 hA)
    _ = (5 * (6 * Real.sqrt d)) ^ d / κ * (r / s) ^ d * (κ * (3 ^ m) ^ d) := by
        field_simp
    _ ≤ (5 * (6 * Real.sqrt d)) ^ d / κ * (r / s) ^ d *
        ((componentEuclideanBall C z s).card : ℝ) :=
        mul_le_mul_of_nonneg_left hcount (by positivity)

theorem inner_smul_inv_norm_self (p : EuclideanSpace ℝ (Fin d)) (c : ℝ) :
    inner ℝ p ((c * ‖p‖⁻¹) • p) = c * ‖p‖ := by
  rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
  rcases eq_or_ne ‖p‖ 0 with h | h
  · rw [h]; simp
  · field_simp

theorem norm_smul_inv_norm_self_le (p : EuclideanSpace ℝ (Fin d)) {c : ℝ} (hc : 0 ≤ c) :
    ‖(c * ‖p‖⁻¹) • p‖ ≤ c := by
  rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hc, abs_inv, abs_norm]
  rcases eq_or_ne ‖p‖ 0 with h | h
  · rw [h]; simp [hc]
  · rw [mul_assoc, inv_mul_cancel₀ h, mul_one]

/-- **Cap density of cluster balls** from the density in cubes. -/
theorem clusterBallCapDensity_of_clusterCubeDensity (C : OpenComponent ω) (z : Vertex d)
    {ℓ κ : ℝ} (R : ℝ) (hd : 0 < d) (hκ : 0 < κ)
    (hcube : ClusterCubeDensity C z (24 * Real.sqrt d) ℓ κ) :
    ClusterBallCapDensity C z (24 * Real.sqrt d * max ℓ 1) R
      (κ / (5 * (24 * Real.sqrt d)) ^ d) := by
  classical
  intro ρ hρ hρR
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 (Nat.cast_pos.2 hd)
  have hsd1 : 1 ≤ Real.sqrt d := Real.one_le_sqrt.2 (Nat.one_le_cast.2 hd)
  have hmax1 : 1 ≤ max ℓ 1 := le_max_right _ _
  have hρ24 : 24 * Real.sqrt d ≤ ρ := by nlinarith
  have hρℓ : 24 * Real.sqrt d * ℓ ≤ ρ :=
    (mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)).trans hρ
  have hρ0 : 0 < ρ := by linarith
  have hρ1 : 1 ≤ ρ := by nlinarith
  have hx : 1 ≤ ρ / (8 * Real.sqrt d) := by rw [le_div_iff₀ (by positivity)]; linarith
  obtain ⟨m, hm1, hm2⟩ := exists_nat_pow_near hx (by norm_num : (1 : ℝ) < 3)
  have h3m : ρ / (24 * Real.sqrt d) < 3 ^ m := by
    rw [pow_succ] at hm2
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ (by positivity)] at hm2
    linarith
  have hℓ : ℓ ≤ 3 ^ m := by
    refine le_trans ?_ h3m.le
    rw [le_div_iff₀ (by positivity)]; linarith
  have hsm : Real.sqrt d * 3 ^ m ≤ ρ / 8 := by
    rw [le_div_iff₀ (by positivity)] at hm1
    linarith
  -- the count in a cap
  have hcap : ∀ σ : ℝ, |σ| = 1 → ∀ p : EuclideanSpace ℝ (Fin d),
      κ * 3 ^ (d * m) ≤ ((componentEuclideanBall C z ρ).filter fun x =>
        ‖p‖ * ρ / 2 ≤ σ * inner ℝ p (latticeEuclideanEmbedding x.val -
          latticeEuclideanEmbedding z)).card := by
    intro σ hσ p
    set w := latticeEuclideanEmbedding z + ((σ * (3 * ρ / 4)) * ‖p‖⁻¹) • p with hw
    have hwz : dist w (latticeEuclideanEmbedding z) ≤ 3 * ρ / 4 := by
      rw [hw, dist_eq_norm, add_sub_cancel_left]
      calc ‖((σ * (3 * ρ / 4)) * ‖p‖⁻¹) • p‖ = |σ| * ‖((3 * ρ / 4) * ‖p‖⁻¹) • p‖ := by
            rw [mul_assoc, ← smul_smul, norm_smul, Real.norm_eq_abs]
        _ ≤ 3 * ρ / 4 := by
            rw [hσ, one_mul]; exact norm_smul_inv_norm_self_le p (by positivity)
    have hρ24 : ρ ≤ 24 * Real.sqrt d * 3 ^ m := by
      rw [pow_succ, div_lt_iff₀ (by positivity)] at hm2
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 3) m]
    refine le_card_filter_of_clusterCubeDensity C z hcube hℓ (by linarith) hρ24 _ ?_
    intro x hx
    have hsplit : inner ℝ p (latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding z) =
        σ * (3 * ρ / 4) * ‖p‖ + inner ℝ p (latticeEuclideanEmbedding x.val - w) := by
      have : latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding z =
          ((σ * (3 * ρ / 4)) * ‖p‖⁻¹) • p + (latticeEuclideanEmbedding x.val - w) := by
        rw [hw]; abel
      rw [this, inner_add_right, inner_smul_inv_norm_self]
    have hcs : |inner ℝ p (latticeEuclideanEmbedding x.val - w)| ≤ ‖p‖ * (ρ / 8) := by
      refine (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
      rw [← dist_eq_norm]; linarith
    rw [hsplit, mul_add, ← mul_assoc, ← mul_assoc, ← abs_mul_abs_self σ, hσ]
    have hσi : |σ * inner ℝ p (latticeEuclideanEmbedding x.val - w)| ≤ ‖p‖ * (ρ / 8) := by
      rw [abs_mul, hσ, one_mul]; exact hcs
    have := (abs_le.1 hσi).1
    nlinarith [mul_nonneg hρ0.le (norm_nonneg p)]
  have hplus := hcap 1 abs_one
  have hminus := hcap (-1) (by simp)
  have hpos : 0 < (componentEuclideanBall C z ρ).card := by
    have h0 := hplus 0
    have : (0 : ℝ) < ((componentEuclideanBall C z ρ).card : ℝ) :=
      (by positivity : (0 : ℝ) < κ * 3 ^ (d * m)).trans_le
        (h0.trans (Nat.cast_le.2 (Finset.card_filter_le _ _)))
    exact_mod_cast this
  have hball : (κ / (5 * (24 * Real.sqrt d)) ^ d) *
      ((componentEuclideanBall C z ρ).card : ℝ) ≤ κ * 3 ^ (d * m) := by
    have h1 : ((componentEuclideanBall C z ρ).card : ℝ) ≤ (5 * ρ) ^ d :=
      (card_componentEuclideanBall_le C z hρ0.le).trans
        (pow_le_pow_left₀ (by linarith) (by linarith) d)
    have h2 : (κ / (5 * (24 * Real.sqrt d)) ^ d) * (5 * ρ) ^ d =
        κ * (ρ / (24 * Real.sqrt d)) ^ d := by
      rw [div_mul_eq_mul_div, mul_div_assoc, ← div_pow]
      congr 2
      field_simp
    have h3 : (ρ / (24 * Real.sqrt d)) ^ d ≤ (3 : ℝ) ^ (d * m) := by
      rw [show d * m = m * d from mul_comm d m, pow_mul]
      exact pow_le_pow_left₀ (by positivity) h3m.le d
    calc (κ / (5 * (24 * Real.sqrt d)) ^ d) * ((componentEuclideanBall C z ρ).card : ℝ)
        ≤ (κ / (5 * (24 * Real.sqrt d)) ^ d) * (5 * ρ) ^ d :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = κ * (ρ / (24 * Real.sqrt d)) ^ d := h2
      _ ≤ κ * 3 ^ (d * m) := mul_le_mul_of_nonneg_left h3 hκ.le
  refine ⟨hpos, fun p => ⟨?_, ?_⟩⟩
  · refine hball.trans ((hplus p).trans (le_of_eq ?_))
    congr 2
    ext x
    simp
  · refine hball.trans ((hminus p).trans (le_of_eq ?_))
    congr 2
    ext x
    simp only [Finset.mem_filter, neg_mul, one_mul]
    constructor <;> intro h <;> refine ⟨h.1, by linarith [h.2]⟩

end Rigidity.Proofs.Regularity
