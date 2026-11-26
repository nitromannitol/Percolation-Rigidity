import Rigidity.Proofs.Corrector.PlanarMeasurableCorrector
import LatticeProb.Prob.Percolation.LatticeLocalGradient
import PercolationClusterHomogenization.Proofs.Regularity.GeneralOrderZeroHolds
import PercolationClusterHomogenization.Proofs.Regularity.PlanarCorrectorConstruction

/-!
# The Lipschitz bound of the corrector in every dimension

Dario's Proposition 2.15 bounds the gradient of the corrector by `C |p| 𝒳^{d/2}` with the minimal
scale `𝒳` of the regularity theory, Proposition 2.14 (Armstrong–Dario, Theorem 2(iii) at order
zero, with the Caccioppoli inequality). Here, in dimension `d ≥ 2`:

* the order-zero regularity (`Rigidity.Proofs.Regularity.armstrongDarioOrderZero_holds`, with a
  minimal scale `X ≤ O_s(θ)`) approximates a corrected plane on `B_{5r}` by a constant up to
  `C₀ (5r/R) ‖ℓ - ℓ(b)‖_{B_R}`;
* the local gradient bound of the cluster (`component_local_gradient`, from the Caccioppoli
  inequality) bounds an edge at the origin by `r^{(d-2)/2}` times the `L²` norm on `B_{4r}`;
* letting `R → ∞`, the sublinearity of the corrected plane gives
  `|ℓ(a) - ℓ(b)| ≤ L max(X, 2)^d Σ |q_i|` for every open edge `ab` at the origin
  (`lipschitz_correctedPlane_origin`).

The power `max(X, 2)^d` (instead of `X^{d/2}` of the paper) comes from bounding the cluster ball
`B_{4r}` by the lattice ball `B_{5r}` without Caccioppoli's inequality at the scale `5r`; it is
again `O_{s/d}(C)`.
-/

namespace Rigidity.Corrector.GeneralDim

open MeasureTheory Filter LatticeProb.Percolation Rigidity.External
open scoped Classical

variable {d : ℕ}

/-- Elements of a one-dimensional `harmonicGrowthSpace C 0` are constant. -/
theorem harmonicGrowthSpace_zero_const {ω : Configuration d} {C : OpenComponent ω} (a₀ : C)
    (h1 : Module.finrank ℝ (harmonicGrowthSpace C 0) = 1) {φ : C → ℝ}
    (hφ : φ ∈ harmonicGrowthSpace C 0) (a b : C) : φ a = φ b := by
  have hv : (⟨fun _ => 1, const_mem_harmonicGrowthSpace C 0 1⟩ : harmonicGrowthSpace C 0) ≠ 0 := by
    intro h
    have := congrArg (fun v : harmonicGrowthSpace C 0 => (v : C → ℝ) a₀) h
    simp at this
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hv).1 h1 ⟨φ, hφ⟩
  have ha := congrArg (fun v : harmonicGrowthSpace C 0 => (v : C → ℝ) a) hc
  have hb := congrArg (fun v : harmonicGrowthSpace C 0 => (v : C → ℝ) b) hc
  simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul, mul_one] at ha hb
  rw [← ha, ← hb]

theorem sq_componentBallL2 {ω : Configuration d} (C : OpenComponent ω) (z : Vertex d) (r : ℝ)
    (f : C → ℝ) : componentBallL2 C z r f ^ 2 =
      (∑ x ∈ componentEuclideanBall C z r, f x ^ 2) /
        ((componentEuclideanBall C z r).card : ℝ) :=
  Real.sq_sqrt (div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg _))

/-- The normalized `L²` norm on a ball is at most a pointwise bound. -/
theorem componentBallL2_le_of_abs_le {ω : Configuration d} (C : OpenComponent ω) (z : Vertex d)
    (r : ℝ) (f : C → ℝ) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ x ∈ componentEuclideanBall C z r, |f x| ≤ M) : componentBallL2 C z r f ≤ M := by
  unfold componentBallL2
  rw [Real.sqrt_le_left hM0]
  rcases Nat.eq_zero_or_pos (componentEuclideanBall C z r).card with h0 | hpos
  · rw [h0, Nat.cast_zero, div_zero]
    positivity
  · rw [div_le_iff₀ (by exact_mod_cast hpos)]
    calc ∑ x ∈ componentEuclideanBall C z r, f x ^ 2
        ≤ ∑ _x ∈ componentEuclideanBall C z r, M ^ 2 := Finset.sum_le_sum fun x hx => by
          have := hM x hx
          nlinarith [abs_nonneg (f x), sq_abs (f x)]
      _ = M ^ 2 * (componentEuclideanBall C z r).card := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- The squared normalized `L²` norm on a smaller ball through a larger one. -/
theorem sq_componentBallL2_le_of_subset {ω : Configuration d} (C : OpenComponent ω)
    {z z' : Vertex d} {r r' : ℝ} (f : C → ℝ)
    (hsub : componentEuclideanBall C z r ⊆ componentEuclideanBall C z' r')
    (hne : (componentEuclideanBall C z r).Nonempty) :
    componentBallL2 C z r f ^ 2 ≤
      ((componentEuclideanBall C z' r').card : ℝ) * componentBallL2 C z' r' f ^ 2 := by
  rw [sq_componentBallL2, sq_componentBallL2]
  have hc : (1 : ℝ) ≤ (componentEuclideanBall C z r).card := by
    exact_mod_cast hne.card_pos
  have hc' : (0 : ℝ) < (componentEuclideanBall C z' r').card := by
    exact_mod_cast (hne.mono hsub).card_pos
  rw [mul_div_cancel₀ _ hc'.ne', div_le_iff₀ (by linarith)]
  have hs : ∑ x ∈ componentEuclideanBall C z r, f x ^ 2 ≤
      ∑ x ∈ componentEuclideanBall C z' r', f x ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _
  have h0 : 0 ≤ ∑ x ∈ componentEuclideanBall C z' r', f x ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  nlinarith

theorem abs_coord_le_norm (x : Vertex d) (i : Fin d) :
    |((x i : ℤ) : ℝ)| ≤ ‖latticeEuclideanEmbedding x‖ := by
  have h := PiLp.norm_apply_le (latticeEuclideanEmbedding x) i
  change ‖((x i : ℤ) : ℝ)‖ ≤ _ at h
  rwa [Real.norm_eq_abs] at h

theorem latticeEuclideanEmbedding_zero : latticeEuclideanEmbedding (0 : Vertex d) = 0 := by
  ext i
  simp [latticeEuclideanEmbedding]

/-- The deterministic part of the Lipschitz bound on one component. -/
theorem abs_sub_le_of_orderZero (hd : 2 ≤ d) {ω : Configuration d} (C : OpenComponent ω)
    {X₀ C₀ K : ℝ} (hC₀ : 0 < C₀) (hK : 0 < K)
    (hfin : Module.finrank ℝ (harmonicGrowthSpace C 0) = 1)
    (hH : ∀ R : ℝ, 2 * X₀ ≤ R → ∀ u : C → ℝ,
      (∀ x ∈ componentEuclideanBall C 0 R,
        (∀ y : C, (componentGraph C).Adj x y → y ∈ componentEuclideanBall C 0 R) →
        componentLaplacian C u x = 0) →
      ∃ φ : C → ℝ, φ ∈ harmonicGrowthSpace C 0 ∧ ∀ r : ℝ, X₀ ≤ r → r ≤ R / 2 →
        componentBallL2 C 0 r (u - φ) ≤ C₀ * (r / R) * componentBallL2 C 0 R u)
    (hloc : ∀ (x y : C) (m : ℝ), 2 ≤ m → ∀ f : C → ℝ, (componentGraph C).Adj x y →
      (∀ z ∈ componentEuclideanBall C x.val (2 * m), componentLaplacian C f z = 0) →
      (f x - f y) ^ 2 ≤ K * m ^ (d - 2) * (componentBallL2 C x.val (4 * m) f) ^ 2)
    {q : Fin d → ℝ} {ℓ : C → ℝ} (hℓ : IsCorrectedPlane C q ℓ) {a b : C}
    (hab : (componentGraph C).Adj a b) (ha : ‖latticeEuclideanEmbedding a.val‖ < 2) :
    |ℓ a - ℓ b| ≤ 10 * 12 ^ d * Real.sqrt K * C₀ * max X₀ 2 ^ d * ∑ i, |q i| := by
  set L : ℝ := 10 * 12 ^ d * Real.sqrt K * C₀ with hL
  have hL0 : 0 < L := by positivity
  set r : ℝ := max X₀ 2 with hr
  have hr2 : 2 ≤ r := le_max_right _ _
  have hXr : X₀ ≤ r := le_max_left _ _
  set Q : ℝ := ∑ i, |q i| with hQ
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hharm : ∀ x, componentLaplacian C ℓ x = 0 := hℓ.1.1
  have key : ∀ ε : ℝ, 0 < ε → |ℓ a - ℓ b| ≤ L * r ^ d * (Q + ε) := by
    intro ε hε
    obtain ⟨R₀, hR₀, hsl⟩ := hℓ.2 ε hε
    set R : ℝ := max R₀ (10 * r) with hRdef
    have hR10 : 10 * r ≤ R := le_max_right _ _
    have hRR₀ : R₀ ≤ R := le_max_left _ _
    have hR0 : 0 < R := by linarith
    set u : C → ℝ := fun x => ℓ x - ℓ b with hu
    have hharmu : ∀ z, componentLaplacian C u z = 0 := by
      intro z
      simp only [componentLaplacian, hu, sub_sub_sub_cancel_right]
      exact hharm z
    obtain ⟨φ, hφ, hbd⟩ := hH R (by linarith) u (fun z _ _ => hharmu z)
    have hconst := harmonicGrowthSpace_zero_const a hfin hφ
    set f : C → ℝ := fun x => u x - φ x with hf
    have hharmf : ∀ z, componentLaplacian C f z = 0 := by
      intro z
      have h1 : componentLaplacian C φ z = 0 := hφ.1 z
      have : componentLaplacian C f z = componentLaplacian C u z - componentLaplacian C φ z := by
        simp only [componentLaplacian, hf, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun _ _ => by ring
      rw [this, hharmu z, h1, sub_zero]
    have hfab : f a - f b = ℓ a - ℓ b := by
      simp only [hf, hu, hconst a b]
      ring
    have hl := hloc a b r hr2 f hab (fun z _ => hharmf z)
    rw [hfab] at hl
    have ha' : dist (latticeEuclideanEmbedding a.val) (latticeEuclideanEmbedding 0) < 2 := by
      rw [dist_eq_norm, latticeEuclideanEmbedding_zero, sub_zero]
      exact ha
    have hsub : componentEuclideanBall C a.val (4 * r) ⊆ componentEuclideanBall C 0 (5 * r) := by
      intro x hx
      rw [mem_componentEuclideanBall] at hx ⊢
      linarith [dist_triangle (latticeEuclideanEmbedding x.val) (latticeEuclideanEmbedding a.val)
        (latticeEuclideanEmbedding 0)]
    have hne : (componentEuclideanBall C a.val (4 * r)).Nonempty :=
      ⟨a, by rw [mem_componentEuclideanBall, dist_self]; linarith⟩
    have hball := sq_componentBallL2_le_of_subset C f hsub hne
    have hcard : ((componentEuclideanBall C 0 (5 * r)).card : ℝ) ≤ (12 * r) ^ d := by
      have h1 := componentEuclideanBall_card_le_box C 0 (5 * r)
      have hceil := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 5 * r by linarith)
      have h2 : 2 * (⌈5 * r⌉₊ : ℝ) + 1 ≤ 12 * r := by linarith
      exact h1.trans (pow_le_pow_left₀ (by positivity) h2 d)
    have hreg := hbd (5 * r) (by linarith) (by linarith)
    have hbR : b ∈ componentEuclideanBall C 0 R := by
      rw [mem_componentEuclideanBall, dist_eq_norm, latticeEuclideanEmbedding_zero, sub_zero]
      have hdist := Rigidity.Proofs.Regularity.dist_le_one_of_lattice_adj_general
        (openGraph_le ω ((C.toSimpleGraph_adj a.2 b.2).1 hab))
      rw [dist_eq_norm] at hdist
      have hnb := norm_le_norm_add_norm_sub' (latticeEuclideanEmbedding b.val)
        (latticeEuclideanEmbedding a.val)
      linarith
    have hsup : componentBallL2 C 0 R u ≤ 2 * R * (Q + ε) := by
      refine componentBallL2_le_of_abs_le C 0 R u (by positivity) fun x hx => ?_
      have h1 := hsl R hRR₀ x hx
      have h2 := hsl R hRR₀ b hbR
      have hxR := (mem_componentEuclideanBall C 0 R x).1 hx
      rw [dist_eq_norm, latticeEuclideanEmbedding_zero, sub_zero] at hxR
      have hbR' := (mem_componentEuclideanBall C 0 R b).1 hbR
      rw [dist_eq_norm, latticeEuclideanEmbedding_zero, sub_zero] at hbR'
      have hslope : |componentSlope C q x - componentSlope C q b| ≤ 2 * R * Q := by
        unfold componentSlope
        rw [← Finset.sum_sub_distrib]
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        rw [hQ, Finset.mul_sum]
        refine Finset.sum_le_sum fun i _ => ?_
        rw [← mul_sub, abs_mul]
        have hxi := abs_coord_le_norm x.val i
        have hbi := abs_coord_le_norm b.val i
        have : |((x.val i : ℤ) : ℝ) - ((b.val i : ℤ) : ℝ)| ≤ 2 * R := by
          refine (abs_sub _ _).trans ?_
          linarith
        nlinarith [abs_nonneg (q i)]
      have : |u x| ≤ |ℓ x - componentSlope C q x| + |componentSlope C q x - componentSlope C q b| +
          |ℓ b - componentSlope C q b| := by
        simp only [hu]
        have e : ℓ x - ℓ b = (ℓ x - componentSlope C q x) +
            (componentSlope C q x - componentSlope C q b) - (ℓ b - componentSlope C q b) := by ring
        rw [e]
        exact (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      nlinarith
    have hstep : (ℓ a - ℓ b) ^ 2 ≤ (L * r ^ d * (Q + ε)) ^ 2 := by
      have e1 : C₀ * (5 * r / R) * (2 * R * (Q + ε)) = 10 * C₀ * r * (Q + ε) := by
        have : C₀ * (5 * r / R) * (2 * R * (Q + ε)) = 10 * C₀ * r * (Q + ε) * (R / R) := by ring
        rw [this, div_self hR0.ne', mul_one]
      have hreg2 : componentBallL2 C 0 (5 * r) f ^ 2 ≤ (10 * C₀ * r * (Q + ε)) ^ 2 := by
        have hl0 := componentBallL2_nonneg C 0 (5 * r) f
        have : componentBallL2 C 0 (5 * r) f ≤ 10 * C₀ * r * (Q + ε) := by
          rw [← e1]
          exact hreg.trans (mul_le_mul_of_nonneg_left hsup (by positivity))
        exact pow_le_pow_left₀ hl0 this 2
      have hr0 : 0 < r := by linarith
      have hrd : r ^ (d - 2) * r ^ d * r ^ 2 = r ^ d * r ^ d := by
        rw [mul_comm (r ^ (d - 2)), mul_assoc, ← pow_add, Nat.sub_add_cancel hd]
      have h12 : (12 : ℝ) ^ d ≤ 12 ^ d * 12 ^ d :=
        le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))
      calc (ℓ a - ℓ b) ^ 2 ≤ K * r ^ (d - 2) * componentBallL2 C a.val (4 * r) f ^ 2 := hl
        _ ≤ K * r ^ (d - 2) * (((componentEuclideanBall C 0 (5 * r)).card : ℝ) *
              componentBallL2 C 0 (5 * r) f ^ 2) :=
            mul_le_mul_of_nonneg_left hball (by positivity)
        _ ≤ K * r ^ (d - 2) * ((12 * r) ^ d * (10 * C₀ * r * (Q + ε)) ^ 2) := by
            gcongr
        _ = 12 ^ d * (K * 100 * C₀ ^ 2 * (Q + ε) ^ 2 * (r ^ (d - 2) * r ^ d * r ^ 2)) := by
            rw [mul_pow]
            ring
        _ ≤ (12 ^ d * 12 ^ d) * (K * 100 * C₀ ^ 2 * (Q + ε) ^ 2 * (r ^ (d - 2) * r ^ d * r ^ 2)) :=
            mul_le_mul_of_nonneg_right h12 (by positivity)
        _ = (L * r ^ d * (Q + ε)) ^ 2 := by
            have hsq : Real.sqrt K ^ 2 = K := Real.sq_sqrt hK.le
            rw [hrd, hL]
            simp only [mul_pow, hsq]
            ring
    have hpos : 0 ≤ L * r ^ d * (Q + ε) := by positivity
    have h := sq_le_sq.1 hstep
    rwa [abs_of_nonneg hpos] at h
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hM : 0 < L * r ^ d := by
    have : (0 : ℝ) < r := by linarith
    positivity
  have := key (δ / (L * r ^ d)) (div_pos hδ hM)
  calc |ℓ a - ℓ b| ≤ L * r ^ d * (Q + δ / (L * r ^ d)) := this
    _ = L * r ^ d * Q + δ := by rw [mul_add, mul_div_cancel₀ _ hM.ne']

/-- **The Lipschitz bound of corrected planes at the origin** (Dario, Proposition 2.15, from
Proposition 2.14 at order zero). -/
theorem lipschitz_correctedPlane_origin [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∃ s θ L : ℝ, 0 < s ∧ 0 < θ ∧ 0 < L ∧ ∃ X : Configuration d → ℝ, Measurable X ∧
      (∀ ω, 0 ≤ X ω) ∧ IsOsBond d p X s θ ∧
      ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω,
        ∀ (q : Fin d → ℝ) (ℓ : uniqueInfiniteComponent h → ℝ),
          IsCorrectedPlane (uniqueInfiniteComponent h) q ℓ →
        ∀ a b : uniqueInfiniteComponent h, (componentGraph (uniqueInfiniteComponent h)).Adj a b →
          ‖latticeEuclideanEmbedding a.val‖ < 2 →
          |ℓ a - ℓ b| ≤ L * max (X ω) 2 ^ d * ∑ i, |q i| := by
  obtain ⟨s, θ, C₀, hs, hθ, hC₀, X, hXm, hX0, hXi, hXb, hae⟩ :=
    Rigidity.Proofs.Regularity.armstrongDarioOrderZero_holds d hd p hpc hp1
  obtain ⟨K, hK, hloc⟩ := component_local_gradient d hd
  refine ⟨s, θ, 10 * 12 ^ d * Real.sqrt K * C₀, hs, hθ, by positivity, X, hXm, hX0, ?_, ?_⟩
  · have e : ∀ ω, max (X ω / θ) 0 = X ω / θ := fun ω => max_eq_left (div_nonneg (hX0 ω) hθ.le)
    unfold IsOsBond
    simp only [e]
    exact ⟨hXi, hXb⟩
  filter_upwards [hae] with ω hω
  intro h q ℓ hℓ a b hab ha
  obtain ⟨_, hall⟩ := hω
  obtain ⟨-, hfin, hH⟩ := hall h
  exact abs_sub_le_of_orderZero hd (uniqueInfiniteComponent h) hC₀ hK hfin hH
    (fun x y m hm f hxy hf => hloc ω _ x y m hm f hxy hf) hℓ hab ha

end Rigidity.Corrector.GeneralDim
