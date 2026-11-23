import Rigidity.Proofs.Regularity.PlanarCorrectorConstruction
import Rigidity.Proofs.Regularity.PlanarCoarseBoundTwo

/-!
# (1.18) in dimension two from the approximation of affine functions on growing balls

`PlanarAffineApproximationTwo` is the input of Step 3 of the proof of Proposition 3.1 of
Armstrong, Kuusi and Mourrat (arXiv:1602.00512v1), for `k = 1`, on the planar cluster: almost
surely, for every slope `q` and every `m` with `3^m ≥ 𝒳`, a function harmonic on `𝒞_∞ ∩ B_{3^m}`
within `K |q| 3^{m(1-δ)}` of `q · x` in `L̲²(𝒞_∞ ∩ B_{3^m})`. In AKM2 it comes from the error
estimate for the Dirichlet problem with affine data (their Proposition 3.2); Armstrong and Dario
(arXiv:1609.09431v2, proof of Theorem 2) use their Theorem 1 in its place.

`planarCorrectorSublinearL2Two_of_affineApproximation` proves (1.18)
(`PlanarCorrectorSublinearL2Two`) from it, the order-zero regularity of Theorem 2 (iii) and the
density of the cluster, by the construction of Step 3 (`exists_harmonic_of_approximations`).
-/

namespace Rigidity.Proofs.Regularity

open Finset Filter Topology MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.Percolation
open Rigidity.External Rigidity.Proofs.S2

/-- The approximation of affine functions by harmonic functions on growing balls of the planar
cluster (the input of AKM2, Proposition 3.1, Step 3, for `k = 1`). -/
def PlanarAffineApproximationTwo : Prop :=
  ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
    ∃ s δ θ K : ℝ, 0 < s ∧ 0 < δ ∧ 0 < θ ∧ 0 ≤ K ∧
      ∃ X : Configuration 2 → ℝ, Measurable X ∧ (∀ ω, 0 ≤ X ω) ∧ IsOsBond 2 p X s θ ∧
        ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω, ∀ q : Fin 2 → ℝ,
          ∀ m : ℕ, X ω ≤ 3 ^ m → ∃ v : uniqueInfiniteComponent h → ℝ,
            HarmonicOnBall (uniqueInfiniteComponent h) v (3 ^ m) ∧
            componentBallL2 (uniqueInfiniteComponent h) 0 (3 ^ m)
                (fun x => v x - componentSlope (uniqueInfiniteComponent h) q x) ≤
              K * (|q 0| + |q 1|) * ((3 : ℝ) ^ m) ^ (1 - δ)

theorem three_pow_rpow_eq {m : ℕ} (δ : ℝ) :
    ((3 : ℝ) ^ m) ^ (1 - δ) = 3 ^ m * ((3 : ℝ) ^ (-δ)) ^ m := by
  rw [Real.rpow_sub (by positivity), Real.rpow_one, Real.rpow_neg (by norm_num), inv_pow]
  have e : ((3 : ℝ) ^ m) ^ δ = ((3 : ℝ) ^ δ) ^ m := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
      Real.rpow_natCast]
  rw [e, div_eq_mul_inv]

theorem abs_componentSlope_le {ω : Configuration 2} (C : OpenComponent ω) (q : Fin 2 → ℝ) {R : ℝ}
    {x : C} (hx : x ∈ componentEuclideanBall C 0 R) :
    |componentSlope C q x| ≤ (|q 0| + |q 1|) * R := by
  rw [mem_componentEuclideanBall] at hx
  unfold componentSlope
  rw [Fin.sum_univ_two]
  have h0 := abs_sub_le_dist_latticeEuclideanEmbedding x.val (0 : Vertex 2) 0
  have h1 := abs_sub_le_dist_latticeEuclideanEmbedding x.val (0 : Vertex 2) 1
  simp only [Pi.zero_apply, Int.cast_zero, sub_zero] at h0 h1
  calc |q 0 * (x.val 0 : ℝ) + q 1 * (x.val 1 : ℝ)| ≤ |q 0| * |(x.val 0 : ℝ)| + |q 1| * |(x.val 1 : ℝ)| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ |q 0| * R + |q 1| * R := by gcongr <;> linarith
    _ = (|q 0| + |q 1|) * R := by ring

/-- **The corrector of one slope with the bound (1.18)** on one configuration, from the
approximations on growing balls, the Lipschitz estimate at the origin and the comparability of the
cluster in consecutive triadic balls. -/
theorem exists_corrector_of_scales {ω : Configuration 2} (C : OpenComponent ω) (q : Fin 2 → ℝ)
    {m₀ : ℕ} {K δ X₀ C₀ ρ : ℝ} (hK : 0 ≤ K) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) (hρ : 1 ≤ ρ)
    (hC₀ : 0 ≤ C₀) (hX₀ : X₀ ≤ 3 ^ m₀)
    (hv : ∀ m, m₀ ≤ m → ∃ v : C → ℝ, HarmonicOnBall C v (3 ^ m) ∧
      componentBallL2 C 0 (3 ^ m) (fun x => v x - componentSlope C q x) ≤
        K * (|q 0| + |q 1|) * ((3 : ℝ) ^ m) ^ (1 - δ))
    (hLip : ∀ R : ℝ, 2 * X₀ ≤ R → ∀ w : C → ℝ, HarmonicOnBall C w R →
      ∃ c : ℝ, ∀ r : ℝ, X₀ ≤ r → r ≤ R / 2 →
        componentBallL2 C 0 r (w - fun _ => c) ≤ C₀ * (r / R) * componentBallL2 C 0 R w)
    (hpos : ∀ m, m₀ ≤ m → 0 < (componentEuclideanBall C 0 ((3 : ℝ) ^ m)).card)
    (hratio : ∀ m, m₀ ≤ m → ((componentEuclideanBall C 0 ((3 : ℝ) ^ (m + 1))).card : ℝ) ≤
      ρ ^ 2 * (componentEuclideanBall C 0 ((3 : ℝ) ^ m)).card) :
    ∃ u : C → ℝ, u ∈ harmonicGrowthSpace C 1 ∧ ∀ r : ℝ, 3 ^ (m₀ + 1) ≤ r →
      componentBallL2 C 0 r (fun x => u x - componentSlope C q x) ≤
        3 * ρ * (K * (1 + (1 + ρ + C₀) * (3 * ρ * (3 : ℝ) ^ (-δ) + 1) +
          C₀ * (3 * ρ * (3 : ℝ) ^ (-δ) + 1) / (1 - (3 : ℝ) ^ (-δ)) +
          (ρ + C₀) * (3 * ρ * (3 : ℝ) ^ (-δ) + 1) / (3 * (3 : ℝ) ^ (-δ) - 1))) *
          (|q 0| + |q 1|) * r ^ (1 - δ) := by
  set ε : ℝ := (3 : ℝ) ^ (-δ) with hεdef
  have hε : 0 < ε := by positivity
  have hε1 : ε < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have h3ε : 1 < 3 * ε := by
    have e : 3 * ε = (3 : ℝ) ^ (1 - δ) := by
      rw [hεdef, Real.rpow_sub (by norm_num), Real.rpow_one, Real.rpow_neg (by norm_num),
        div_eq_mul_inv]
    rw [e]; exact Real.one_lt_rpow (by norm_num) (by linarith)
  set Q := |q 0| + |q 1| with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hv' : ∀ m, m₀ ≤ m → ∃ v : C → ℝ, HarmonicOnBall C v (3 ^ m) ∧
      componentBallL2 C 0 (3 ^ m) (fun x => v x - componentSlope C q x) ≤
        K * Q * 3 ^ m * ε ^ m := by
    intro m hm
    obtain ⟨v, hvh, hvb⟩ := hv m hm
    refine ⟨v, hvh, hvb.trans (le_of_eq ?_)⟩
    rw [three_pow_rpow_eq, hεdef]; ring
  obtain ⟨u, hharm, hb⟩ := exists_harmonic_of_approximations C (componentSlope C q)
    (A := K * Q) (by positivity) hε hε1 h3ε (by linarith) hC₀ hX₀ hv' hLip hpos hratio
  set Γ : ℝ := 1 + (1 + ρ + C₀) * (3 * ρ * ε + 1) + C₀ * (3 * ρ * ε + 1) / (1 - ε) +
    (ρ + C₀) * (3 * ρ * ε + 1) / (3 * ε - 1) with hΓ
  have hΓ0 : 0 ≤ Γ := by
    have : 0 < 1 - ε := by linarith
    have : 0 < 3 * ε - 1 := by linarith
    positivity
  have hA' : K * Q + (1 + ρ + C₀) * (K * Q) * (3 * ρ * ε + 1) +
      C₀ * (K * Q) * (3 * ρ * ε + 1) / (1 - ε) +
      (ρ + C₀) * (K * Q) * (3 * ρ * ε + 1) / (3 * ε - 1) = K * Γ * Q := by
    rw [hΓ]; ring
  -- the bound on every radius
  have hbound : ∀ r : ℝ, 3 ^ (m₀ + 1) ≤ r →
      componentBallL2 C 0 r (fun x => u x - componentSlope C q x) ≤
        3 * ρ * (K * Γ) * Q * r ^ (1 - δ) := by
    intro r hr
    have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr
    set n : ℕ := ⌊r⌋₊ with hn
    have h3n : 3 ^ (m₀ + 1) ≤ n := by
      rw [hn]; apply Nat.le_floor; push_cast; exact hr
    set j : ℕ := Nat.log 3 n + 1 with hj
    have hlow : 3 ^ (j - 1) ≤ n := by
      have h1 : 1 ≤ 3 ^ (m₀ + 1) := Nat.one_le_pow _ _ (by norm_num)
      rw [hj, Nat.add_sub_cancel]; exact Nat.pow_log_le_self 3 (by omega)
    have hhigh : n < 3 ^ j := by rw [hj]; exact Nat.lt_pow_succ_log_self (by norm_num) n
    have hjm : m₀ + 2 ≤ j := by
      have := Nat.le_log_of_pow_le (by norm_num) h3n
      omega
    have hrj : r ≤ 3 ^ j := by
      have h1 : r < n + 1 := Nat.lt_floor_add_one r
      have h2 : ((n + 1 : ℕ) : ℝ) ≤ 3 ^ j := by exact_mod_cast hhigh
      push_cast at h2; linarith
    have hjr : (3 : ℝ) ^ (j - 1) ≤ r := by
      have h1 : ((3 ^ (j - 1) : ℕ) : ℝ) ≤ n := by exact_mod_cast hlow
      have h2 : (n : ℝ) ≤ r := Nat.floor_le hr0.le
      push_cast at h1; linarith
    have hsub : componentEuclideanBall C 0 ((3 : ℝ) ^ (j - 1)) ⊆ componentEuclideanBall C 0 r := by
      intro x hx; rw [mem_componentEuclideanBall] at hx ⊢; linarith
    have hposr : 0 < (componentEuclideanBall C 0 r).card :=
      lt_of_lt_of_le (hpos (j - 1) (by omega)) (Finset.card_le_card hsub)
    have h1 := componentBallL2_le_sqrt_card_div_mul C 0 hrj hposr
      (fun x => u x - componentSlope C q x)
    have hratio' : ((componentEuclideanBall C 0 ((3 : ℝ) ^ j)).card : ℝ) /
        (componentEuclideanBall C 0 r).card ≤ ρ ^ 2 := by
      have hn : (0 : ℝ) < (componentEuclideanBall C 0 r).card := by exact_mod_cast hposr
      rw [div_le_iff₀ hn]
      have hr1 := hratio (j - 1) (by omega)
      rw [show j - 1 + 1 = j by omega] at hr1
      have hc : ((componentEuclideanBall C 0 ((3 : ℝ) ^ (j - 1))).card : ℝ) ≤
          (componentEuclideanBall C 0 r).card := by exact_mod_cast Finset.card_le_card hsub
      nlinarith
    have h2 := hb j (by omega)
    rw [hA'] at h2
    have h3 : (3 : ℝ) ^ j * ε ^ j ≤ 3 * r ^ (1 - δ) := by
      have e : (3 : ℝ) ^ j * ε ^ j = ((3 : ℝ) ^ j) ^ (1 - δ) := by rw [three_pow_rpow_eq, hεdef]
      rw [e]
      have h3j : (3 : ℝ) ^ j ≤ 3 * r := by
        have : (3 : ℝ) ^ j = 3 * 3 ^ (j - 1) := by
          rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ j)]
        rw [this]; linarith
      calc ((3 : ℝ) ^ j) ^ (1 - δ) ≤ (3 * r) ^ (1 - δ) :=
            Real.rpow_le_rpow (by positivity) h3j (by linarith)
        _ = (3 : ℝ) ^ (1 - δ) * r ^ (1 - δ) := Real.mul_rpow (by norm_num) hr0.le
        _ ≤ 3 * r ^ (1 - δ) := by
            have : (3 : ℝ) ^ (1 - δ) ≤ 3 := by
              calc (3 : ℝ) ^ (1 - δ) ≤ (3 : ℝ) ^ (1 : ℝ) :=
                    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
                _ = 3 := Real.rpow_one 3
            exact mul_le_mul_of_nonneg_right this (by positivity)
    calc componentBallL2 C 0 r (fun x => u x - componentSlope C q x)
        ≤ Real.sqrt (((componentEuclideanBall C 0 ((3 : ℝ) ^ j)).card : ℝ) /
            (componentEuclideanBall C 0 r).card) *
            componentBallL2 C 0 ((3 : ℝ) ^ j) (fun x => u x - componentSlope C q x) := h1
      _ ≤ ρ * (K * Γ * Q * 3 ^ j * ε ^ j) := by
          apply mul_le_mul _ h2 (componentBallL2_nonneg _ _ _ _) (by linarith)
          rw [Real.sqrt_le_left (by linarith)]; exact hratio'
      _ = ρ * (K * Γ) * Q * (3 ^ j * ε ^ j) := by ring
      _ ≤ ρ * (K * Γ) * Q * (3 * r ^ (1 - δ)) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 3 * ρ * (K * Γ) * Q * r ^ (1 - δ) := by ring
  refine ⟨u, ⟨hharm, ?_⟩, fun r hr => (hbound r hr).trans (le_of_eq (by rw [hΓ, hεdef]))⟩
  -- the linear growth
  set B : ℝ := 3 * ρ * (K * Γ) * Q + Q with hBdef
  have hev : ∀ᶠ R : ℝ in atTop, (R ^ (1 + 1))⁻¹ * componentBallL2 C 0 R u ≤ B / R := by
    refine Filter.eventually_atTop.2 ⟨max (3 ^ (m₀ + 1)) 1, fun R hR => ?_⟩
    have hR1 : 1 ≤ R := (le_max_right _ _).trans hR
    have hR3 : 3 ^ (m₀ + 1) ≤ R := (le_max_left _ _).trans hR
    have hR0 : 0 < R := by linarith
    have hu : componentBallL2 C 0 R u ≤ B * R := by
      have e : u = fun x => (u x - componentSlope C q x) + componentSlope C q x := by
        funext x; ring
      rw [e]
      refine (Rigidity.Proofs.S2.componentBallL2_add_le C 0 R _ _).trans ?_
      have h1 := hbound R hR3
      have h2 : componentBallL2 C 0 R (componentSlope C q) ≤ Q * R :=
        componentBallL2_le_of_abs_le C 0 R (by positivity) fun x hx => abs_componentSlope_le C q hx
      have h3 : R ^ (1 - δ) ≤ R := by
        calc R ^ (1 - δ) ≤ R ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hR1 (by linarith)
          _ = R := Real.rpow_one R
      have h4 : 3 * ρ * (K * Γ) * Q * R ^ (1 - δ) ≤ 3 * ρ * (K * Γ) * Q * R :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
      calc _ ≤ 3 * ρ * (K * Γ) * Q * R ^ (1 - δ) + Q * R := add_le_add h1 h2
        _ ≤ 3 * ρ * (K * Γ) * Q * R + Q * R := by linarith
        _ = B * R := by rw [hBdef]; ring
    rw [show (R ^ (1 + 1))⁻¹ * componentBallL2 C 0 R u = componentBallL2 C 0 R u / R ^ 2 by
      rw [div_eq_inv_mul]]
    rw [div_le_div_iff₀ (by positivity) hR0]
    nlinarith [componentBallL2_nonneg C 0 R u]
  have hev0 : ∀ᶠ R : ℝ in atTop, 0 ≤ (R ^ (1 + 1))⁻¹ * componentBallL2 C 0 R u := by
    refine Filter.eventually_atTop.2 ⟨0, fun R hR => ?_⟩
    exact mul_nonneg (inv_nonneg.2 (by positivity)) (componentBallL2_nonneg _ _ _ _)
  have hlim : Tendsto (fun R : ℝ => B / R) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim hev0 hev

/-- The ratio of the cluster in consecutive triadic balls, from the density of the cluster. -/
theorem card_ball_bounds {ω : Configuration 2} (C : OpenComponent ω) {ℓ κ : ℝ} (hκ : 0 < κ)
    (hcube : ClusterCubeDensity C 0 54 ℓ κ) {m : ℕ} (hm : 2 ≤ m) (hℓ : ℓ ≤ 3 ^ (m - 2)) :
    0 < (componentEuclideanBall C 0 ((3 : ℝ) ^ m)).card ∧
      ((componentEuclideanBall C 0 ((3 : ℝ) ^ (m + 1))).card : ℝ) ≤
        (Real.sqrt (6561 / κ)) ^ 2 * (componentEuclideanBall C 0 ((3 : ℝ) ^ m)).card := by
  have h := card_componentEuclideanBall_ge C hcube hℓ (x := (0 : Vertex 2)) fun i => by
    simp only [Pi.zero_apply, abs_zero]; positivity
  have e : (9 : ℝ) * 3 ^ (m - 2) = 3 ^ m := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, ← pow_add]; congr 1; omega
  rw [e] at h
  have hpos : (0 : ℝ) < κ * 9 ^ (m - 2) := by positivity
  refine ⟨by exact_mod_cast lt_of_lt_of_le hpos h, ?_⟩
  rw [Real.sq_sqrt (by positivity)]
  have hbig := card_componentEuclideanBall_le C (0 : Vertex 2)
    (by positivity : (0 : ℝ) ≤ 3 ^ (m + 1))
  have hb : (2 * (3 : ℝ) ^ (m + 1) + 3) ^ 2 ≤ 6561 * 9 ^ (m - 2) := by
    have h1 : (2 * (3 : ℝ) ^ (m + 1) + 3) ≤ 3 ^ (m + 2) := by
      have : (3 : ℝ) ≤ 3 ^ (m + 1) := by
        calc (3 : ℝ) = 3 ^ 1 := by norm_num
          _ ≤ 3 ^ (m + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      have e2 : (3 : ℝ) ^ (m + 2) = 3 * 3 ^ (m + 1) := by ring
      linarith
    have e3 : ((3 : ℝ) ^ (m + 2)) ^ 2 = 6561 * 9 ^ (m - 2) := by
      rw [← pow_mul, show (m + 2) * 2 = 8 + 2 * (m - 2) by omega, pow_add, pow_mul]; norm_num
    rw [← e3]
    exact pow_le_pow_left₀ (by positivity) h1 2
  calc ((componentEuclideanBall C 0 ((3 : ℝ) ^ (m + 1))).card : ℝ)
      ≤ (2 * (3 : ℝ) ^ (m + 1) + 3) ^ 2 := hbig
    _ ≤ 6561 * 9 ^ (m - 2) := hb
    _ = 6561 / κ * (κ * 9 ^ (m - 2)) := by field_simp
    _ ≤ 6561 / κ * (componentEuclideanBall C 0 ((3 : ℝ) ^ m)).card :=
        mul_le_mul_of_nonneg_left h (by positivity)

/-- **(1.18) in dimension two** from the approximation of affine functions on growing balls and the
order-zero regularity of Theorem 2 (iii), by Step 3 of AKM2, Proposition 3.1. -/
theorem planarCorrectorSublinearL2Two_of_affineApproximation (hA : PlanarAffineApproximationTwo)
    (hR3 : ArmstrongDarioOrderZeroTwo) : PlanarCorrectorSublinearL2Two := by
  intro p hpc hp1
  obtain ⟨sA, δA, θA, KA, hsA, hδA, hθA, hKA, XA, hXAm, hXA0, hXAos, haeA⟩ := hA p hpc hp1
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = min δA (1 / 2) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδdef]; exact lt_min hδA (by norm_num)
  have hδ2 : δ ≤ 1 / 2 := by rw [hδdef]; exact min_le_right _ _
  have hδδ : δ ≤ δA := by rw [hδdef]; exact min_le_left _ _
  obtain ⟨s₃, θ₃, C₀, hs₃, hθ₃, hC₀, X₃, hX₃m, hX₃0, hX₃i, hX₃b, hae₃⟩ :=
    exists_planar_origin_constant_approximation hR3 p hpc hp1
  have hX₃os : IsOsBond 2 p X₃ s₃ θ₃ := by
    have e : ∀ ω, max (X₃ ω / θ₃) 0 = X₃ ω / θ₃ := fun ω => max_eq_left (div_nonneg (hX₃0 ω) hθ₃.le)
    unfold IsOsBond
    simp only [e]
    exact ⟨hX₃i, hX₃b⟩
  have hθp : 0 < theta 2 p := Rigidity.Percolation.theta_pos_of_criticalProbability_lt 2 p hpc
  obtain ⟨s₄, θ₄, hs₄, hθ₄, hcube⟩ := exists_clusterCubeDensity_of_concentration (d := 2) le_rfl p
    (cluster_density_concentration 2 le_rfl p hpc hp1) 54
  obtain ⟨M₄, hM₄m, hM₄0, hM₄os, hM₄ae⟩ := hcube 0
  set κ : ℝ := theta 2 p / 2 with hκdef
  have hκ : 0 < κ := by positivity
  have hκ1 : κ ≤ 1 := by
    have := theta_le_one 2 p
    rw [hκdef]; linarith
  set ρ : ℝ := Real.sqrt (6561 / κ) with hρdef
  have hρ1 : 1 ≤ ρ := by
    rw [hρdef, Real.le_sqrt (by norm_num) (by positivity), one_pow, le_div_iff₀ hκ]; linarith
  -- the minimal scale
  set Mx : Configuration 2 → ℝ := fun ω => max (max (XA ω) (X₃ ω)) (max (81 * M₄ ω) 81) with hMx
  obtain ⟨θ₁, hθ₁, h1⟩ := exists_isOsBond_max hsA hs₃ hθA hθ₃ hXAm hX₃m hXAos hX₃os
  have h81 := IsOsBond.const_mul (by norm_num : (0 : ℝ) < 81) hM₄os
  obtain ⟨θ₂, hθ₂, h2⟩ := exists_isOsBond_max hs₄ hs₄ (by positivity) (by positivity)
    (hM₄m.const_mul 81) measurable_const h81
    (isOsBond_const (p := p) (d := 2) (by norm_num : (0 : ℝ) < 81) hs₄)
  obtain ⟨θ₃', hθ₃', h3⟩ := exists_isOsBond_max (lt_min hsA hs₃) (lt_min hs₄ hs₄) hθ₁ hθ₂
    (hXAm.max hX₃m) ((hM₄m.const_mul 81).max measurable_const) h1 h2
  have hXos := IsOsBond.const_mul (by norm_num : (0 : ℝ) < 18) h3
  set Γ : ℝ := 1 + (1 + ρ + C₀) * (3 * ρ * (3 : ℝ) ^ (-δ) + 1) +
    C₀ * (3 * ρ * (3 : ℝ) ^ (-δ) + 1) / (1 - (3 : ℝ) ^ (-δ)) +
    (ρ + C₀) * (3 * ρ * (3 : ℝ) ^ (-δ) + 1) / (3 * (3 : ℝ) ^ (-δ) - 1) with hΓ
  have hε1 : (3 : ℝ) ^ (-δ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have h3ε : 1 < 3 * (3 : ℝ) ^ (-δ) := by
    have e : 3 * (3 : ℝ) ^ (-δ) = (3 : ℝ) ^ (1 - δ) := by
      rw [Real.rpow_sub (by norm_num), Real.rpow_one, Real.rpow_neg (by norm_num), div_eq_mul_inv]
    rw [e]; exact Real.one_lt_rpow (by norm_num) (by linarith)
  have hΓ0 : 0 ≤ Γ := by
    have : 0 < 1 - (3 : ℝ) ^ (-δ) := by linarith
    have : 0 < 3 * (3 : ℝ) ^ (-δ) - 1 := by linarith
    positivity
  refine ⟨_, δ, _, 3 * ρ * (KA * Γ), lt_min (lt_min hsA hs₃) (lt_min hs₄ hs₄), hδ0, by positivity,
    by positivity, fun ω => 18 * Mx ω,
    ((hXAm.max hX₃m).max ((hM₄m.const_mul 81).max measurable_const)).const_mul 18,
    fun ω => by have : (0 : ℝ) ≤ Mx ω := le_trans (by norm_num) (le_max_right _ _ |>.trans
      (le_max_right _ _)); positivity, hXos, ?_⟩
  filter_upwards [haeA, hae₃, hM₄ae] with ω hωA hω₃ hω₄
  intro h q
  obtain ⟨-, hω₃'⟩ := hω₃
  have hLip := hω₃' h
  -- the scale `m₀`
  have hMx81 : 81 ≤ Mx ω := (le_max_right _ _).trans (le_max_right _ _)
  set n : ℕ := ⌈Mx ω⌉₊ with hn
  set m₀ : ℕ := Nat.log 3 n + 1 with hm₀
  have hn81 : 81 ≤ n := by
    rw [hn]; exact_mod_cast (hMx81.trans (Nat.le_ceil _))
  have hMxm : Mx ω ≤ 3 ^ m₀ := by
    have h1 : Mx ω ≤ n := Nat.le_ceil _
    have h2 : n < 3 ^ m₀ := by rw [hm₀]; exact Nat.lt_pow_succ_log_self (by norm_num) n
    have h3 : ((n : ℕ) : ℝ) ≤ ((3 ^ m₀ : ℕ) : ℝ) := by exact_mod_cast h2.le
    push_cast at h3; linarith
  have hm₀5 : 5 ≤ m₀ := by
    have : 4 ≤ Nat.log 3 n := Nat.le_log_of_pow_le (by norm_num) (by norm_num; omega)
    omega
  have hXm₀ : (3 : ℝ) ^ (m₀ + 1) ≤ 18 * Mx ω := by
    have h1 : 3 ^ (m₀ - 1) ≤ n := by
      rw [hm₀, Nat.add_sub_cancel]; exact Nat.pow_log_le_self 3 (by omega)
    have h2 : (n : ℝ) ≤ Mx ω + 1 := (Nat.ceil_lt_add_one (by linarith)).le
    have h3 : ((3 ^ (m₀ - 1) : ℕ) : ℝ) ≤ n := by exact_mod_cast h1
    have e : (3 : ℝ) ^ (m₀ + 1) = 9 * 3 ^ (m₀ - 1) := by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, ← pow_add]; congr 1; omega
    push_cast at h3
    rw [e]; linarith
  have hXA : XA ω ≤ 3 ^ m₀ := ((le_max_left _ _).trans (le_max_left _ _)).trans hMxm
  have hX3 : X₃ ω ≤ 3 ^ m₀ := ((le_max_right _ _).trans (le_max_left _ _)).trans hMxm
  have hM4 : 81 * M₄ ω ≤ 3 ^ m₀ := ((le_max_left _ _).trans (le_max_right _ _)).trans hMxm
  have hle : ∀ m, m₀ ≤ m → (3 : ℝ) ^ m₀ ≤ 3 ^ m := fun m hm => pow_le_pow_right₀ (by norm_num) hm
  have hballs : ∀ m, m₀ ≤ m → 0 < (componentEuclideanBall (uniqueInfiniteComponent h) 0
      ((3 : ℝ) ^ m)).card ∧
      ((componentEuclideanBall (uniqueInfiniteComponent h) 0 ((3 : ℝ) ^ (m + 1))).card : ℝ) ≤
        ρ ^ 2 * (componentEuclideanBall (uniqueInfiniteComponent h) 0 ((3 : ℝ) ^ m)).card := by
    intro m hm
    refine card_ball_bounds _ hκ (hω₄ h) (by omega) ?_
    have h1 : 81 * M₄ ω ≤ 3 ^ m := hM4.trans (hle m hm)
    have e : (3 : ℝ) ^ m = 9 * 3 ^ (m - 2) := by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, ← pow_add]; congr 1; omega
    have h0 := hM₄0 ω
    have : (0 : ℝ) ≤ 3 ^ (m - 2) := by positivity
    rw [e] at h1; linarith
  obtain ⟨u, hu, hb⟩ := exists_corrector_of_scales (uniqueInfiniteComponent h) q (m₀ := m₀)
    (K := KA) (δ := δ) (X₀ := X₃ ω) (C₀ := C₀) (ρ := ρ) hKA hδ0 hδ2 hρ1 hC₀.le hX3
    (fun m hm => by
      obtain ⟨v, hvh, hvb⟩ := hωA h q m (hXA.trans (hle m hm))
      refine ⟨v, hvh, hvb.trans ?_⟩
      have h3m : (1 : ℝ) ≤ 3 ^ m := one_le_pow₀ (by norm_num)
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h3m (by linarith))
        (by positivity))
    hLip (fun m hm => (hballs m hm).1) (fun m hm => (hballs m hm).2)
  refine ⟨u, hu, fun r hr => ?_⟩
  refine (hb r (hXm₀.trans hr)).trans (le_of_eq ?_)
  rw [hΓ]

/-- **Every slope has a corrected plane on the planar cluster**, from the approximation of affine
functions on growing balls, the order-zero regularity and the minimal scales of Proposition 2.4. -/
theorem planarCorrectedPlaneExistenceTwo_of_affineApproximation
    (hA : PlanarAffineApproximationTwo) (hR3 : ArmstrongDarioOrderZeroTwo)
    (hM5 : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      PlanarMinimalScalesTwo p) :
    PlanarCorrectedPlaneExistenceTwo :=
  planarCorrectedPlaneExistenceTwo_of_sublinearL2
    (planarCorrectorSublinearL2Two_of_affineApproximation hA hR3) hR3 hM5

end Rigidity.Proofs.Regularity
