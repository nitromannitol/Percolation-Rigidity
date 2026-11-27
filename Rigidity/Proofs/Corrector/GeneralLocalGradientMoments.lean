import Rigidity.Proofs.Corrector.GeneralLocalGradientProb
import Rigidity.Proofs.Corrector.GeneralCorrectorLipschitz
import Rigidity.Proofs.Corrector.DarioLocalGradientMoments
import Rigidity.Proofs.Green.GeneralFluxMoments
import Rigidity.Proofs.Green.GeneralFluxBox

/-!
# Moments of the local gradient bound on `ℤᵈ`

On the event of the order-zero regularity (Armstrong and Dario, Theorem 2 (iii) at `k = 0`, with a
minimal scale `X`), every admissible function at scale `R ≥ 10 max(X, 2)` is harmonic on the cluster
in the ball of radius `R` and within `3R` of a constant there, so it is approximated on the ball of
radius `5 max(X, 2)` by a constant up to `15 C₀ max(X, 2)`, and the local gradient bound of the
cluster (`component_local_gradient`) bounds it along the edges at the origin by
`15 · 12^d √K C₀ max(X, 2)^d` (`localGrad_le_of_orderZero`, the argument of
`abs_sub_le_of_orderZero` for a function harmonic in a ball). When `R < 10 max(X, 2)` the bound
`localGrad ≤ 6R` gives the same form, and when the origin is in the local cluster but not in the
infinite cluster it lies in a finite cluster of at least `R + 1` points. Hence (`ae_localGrad_le`)

`localGrad R ω ≤ L max(X, 2)^d + 6R 1{the origin is in a finite cluster of at least R + 1 points}`,

whose moments are bounded uniformly in `R` for `d ≥ 3` (`growthMoments_localGrad`).

This is the planar file `DarioLocalGradientMoments` on `ℤᵈ`. The order-zero regularity and the
local gradient bound of the cluster are their `d`-dimensional forms
(`armstrongDarioOrderZero_holds`, `component_local_gradient d`), the factor `m^{d-2}` of the latter
and the `(12 r)^d` points of the ball of radius `5r` turn the power `max(X, 2)²` into
`max(X, 2)^d`, and the planar tail `C exp(-c √N)` of the finite clusters becomes
`C exp(-c N^{1/d})` (`exists_finite_cluster_card_le`, `d ≥ 3`). The moments are written with
`GrowthMomentsD`: those of `max(X, 2)^d` come from its `𝒪_s` bound (`GrowthMomentsD.pow_nat`), and
those of the finite cluster term from `x^a e^{-c x} ≤ (a/c)^a` (`rpow_mul_exp_neg_le`) at
`x = (R + 1)^{1/d}`.
-/

namespace Rigidity.Corrector.GeneralDim

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Poincare.GeneralDim
open Rigidity.Green.GeneralFlux (GrowthMomentsD growthMomentsD_of_isOsBond)
open scoped Classical ENNReal

variable {d : ℕ}

theorem localGrad_eq_zero_of_not_mem {ω : Configuration d} {R : ℕ} (hR : 1 ≤ R)
    (h0 : (0 : Vertex d) ∉ localCluster R ω) : localGrad R ω = 0 := by
  refine le_antisymm (csSup_le (Set.insert_nonempty _ _) fun t ht => ?_)
    (localGrad_nonneg ω hR)
  rcases ht with rfl | ⟨_, _, _, h0', _, _⟩
  · exact le_rfl
  · exact absurd h0' h0

theorem mem_supBox_of_norm_le {x : Vertex d} {R : ℕ}
    (h : ‖latticeEuclideanEmbedding x‖ ≤ R) : x ∈ supBox (0 : Vertex d) R := by
  rw [mem_supBox]
  intro i
  have := (abs_coord_le_norm x i).trans h
  simp only [Pi.zero_apply, sub_zero]
  exact_mod_cast this

/-- **The local gradient bound through the order-zero regularity** (deterministic). -/
theorem localGrad_le_of_orderZero (hd : 2 ≤ d) {ω : Configuration d}
    (hu : HasUniqueInfiniteOpenComponent ω) {X₀ C₀ K : ℝ} (hC₀ : 0 < C₀) (hK : 0 < K)
    (hfin : Module.finrank ℝ (harmonicGrowthSpace (uniqueInfiniteComponent hu) 0) = 1)
    (hH : ∀ R : ℝ, 2 * X₀ ≤ R → ∀ u : uniqueInfiniteComponent hu → ℝ,
      (∀ x ∈ componentEuclideanBall (uniqueInfiniteComponent hu) 0 R,
        (∀ y : uniqueInfiniteComponent hu,
          (componentGraph (uniqueInfiniteComponent hu)).Adj x y →
            y ∈ componentEuclideanBall (uniqueInfiniteComponent hu) 0 R) →
        componentLaplacian (uniqueInfiniteComponent hu) u x = 0) →
      ∃ φ : uniqueInfiniteComponent hu → ℝ, φ ∈ harmonicGrowthSpace (uniqueInfiniteComponent hu) 0 ∧
        ∀ r : ℝ, X₀ ≤ r → r ≤ R / 2 →
          componentBallL2 (uniqueInfiniteComponent hu) 0 r (u - φ) ≤
            C₀ * (r / R) * componentBallL2 (uniqueInfiniteComponent hu) 0 R u)
    (hloc : ∀ (x y : uniqueInfiniteComponent hu) (m : ℝ), 2 ≤ m →
      ∀ f : uniqueInfiniteComponent hu → ℝ,
      (componentGraph (uniqueInfiniteComponent hu)).Adj x y →
      (∀ z ∈ componentEuclideanBall (uniqueInfiniteComponent hu) x.val (2 * m),
        componentLaplacian (uniqueInfiniteComponent hu) f z = 0) →
      (f x - f y) ^ 2 ≤ K * m ^ (d - 2) *
        (componentBallL2 (uniqueInfiniteComponent hu) x.val (4 * m) f) ^ 2)
    (h0 : (0 : Vertex d) ∈ (uniqueInfiniteComponent hu).supp) {R : ℕ}
    (hR : 10 * max X₀ 2 ≤ R) :
    localGrad R ω ≤ 15 * 12 ^ d * Real.sqrt K * C₀ * max X₀ 2 ^ d := by
  set C := uniqueInfiniteComponent hu with hCdef
  set r : ℝ := max X₀ 2 with hr
  have hr2 : 2 ≤ r := le_max_right _ _
  have hr0 : 0 < r := by linarith
  have hXr : X₀ ≤ r := le_max_left _ _
  have hR0 : (0 : ℝ) < R := by linarith
  have hICE : ∀ y ∈ C.supp, ω ∈ infiniteComponentEvent y := fun y hy =>
    (mem_uniqueInfiniteComponent_iff hu y).1 hy
  refine csSup_le (Set.insert_nonempty _ _) fun t ht => ?_
  rcases ht with rfl | ⟨h, w, ⟨hharmh, c, hc⟩, h0L, hw, rfl⟩
  · positivity
  set u : C → ℝ := fun x => h x.val - c with hu'
  have hharm : ∀ x ∈ componentEuclideanBall C 0 R,
      (∀ y : C, (componentGraph C).Adj x y → y ∈ componentEuclideanBall C 0 R) →
        componentLaplacian C u x = 0 := by
    intro x hx hall
    have hxR := (mem_componentEuclideanBall C 0 R x).1 hx
    rw [dist_eq_norm, GeneralDim.latticeEuclideanEmbedding_zero, sub_zero] at hxR
    have hxB := mem_supBox_of_norm_le (R := R) hxR.le
    have hxL := mem_localCluster_of_infinite hxB (hICE x.val x.2)
    have hlap : openLaplacian ω h x.val = 0 := by
      refine hharmh x.val hxL fun w' hw' => ?_
      have hw'C : w' ∈ C.supp := C.mem_supp_of_adj_mem_supp x.2 hw'
      have hadj : (componentGraph C).Adj x ⟨w', hw'C⟩ := (C.toSimpleGraph_adj x.2 hw'C).2 hw'
      have hy := (mem_componentEuclideanBall C 0 R _).1 (hall _ hadj)
      rw [dist_eq_norm, GeneralDim.latticeEuclideanEmbedding_zero, sub_zero] at hy
      exact mem_supBox_of_norm_le hy.le
    have e : componentLaplacian C u x = componentLaplacian C (fun y => h y.val) x := by
      simp only [componentLaplacian, hu', sub_sub_sub_cancel_right]
    rw [e, componentLaplacian_restrict_eq C h x]
    exact hlap
  have hsup : componentBallL2 C 0 R u ≤ 3 * R := by
    refine componentBallL2_le_of_abs_le C 0 R u (by positivity) fun x hx => ?_
    have hxR := (mem_componentEuclideanBall C 0 R x).1 hx
    rw [dist_eq_norm, GeneralDim.latticeEuclideanEmbedding_zero, sub_zero] at hxR
    exact hc x.val (mem_localCluster_of_infinite (mem_supBox_of_norm_le hxR.le) (hICE x.val x.2))
  obtain ⟨φ, hφ, hbd⟩ := hH R (by linarith) u hharm
  set a : C := ⟨0, h0⟩ with ha
  have hwC : w ∈ C.supp := C.mem_supp_of_adj_mem_supp h0 hw
  set b : C := ⟨w, hwC⟩ with hb
  have hab : (componentGraph C).Adj a b := (C.toSimpleGraph_adj h0 hwC).2 hw
  have hconst := harmonicGrowthSpace_zero_const a hfin hφ
  set f : C → ℝ := fun x => u x - φ x with hf
  have hharmf : ∀ z ∈ componentEuclideanBall C a.val (2 * r), componentLaplacian C f z = 0 := by
    intro z hz
    have h1 : componentLaplacian C φ z = 0 := hφ.1 z
    have hz' := (mem_componentEuclideanBall C a.val (2 * r) z).1 hz
    rw [dist_eq_norm, show a.val = 0 from rfl, GeneralDim.latticeEuclideanEmbedding_zero,
      sub_zero] at hz'
    have hzR : z ∈ componentEuclideanBall C 0 R := by
      rw [mem_componentEuclideanBall, dist_eq_norm, GeneralDim.latticeEuclideanEmbedding_zero,
        sub_zero]
      linarith
    have hall : ∀ y : C, (componentGraph C).Adj z y → y ∈ componentEuclideanBall C 0 R := by
      intro y hy
      rw [mem_componentEuclideanBall, dist_eq_norm, GeneralDim.latticeEuclideanEmbedding_zero,
        sub_zero]
      have hadj := (C.toSimpleGraph_adj z.2 y.2).1 hy
      have hdist := Rigidity.Proofs.Regularity.dist_le_one_of_lattice_adj_general
        (openGraph_le ω hadj)
      rw [dist_eq_norm] at hdist
      have hnb := norm_le_norm_add_norm_sub' (latticeEuclideanEmbedding y.val)
        (latticeEuclideanEmbedding z.val)
      linarith
    have : componentLaplacian C f z = componentLaplacian C u z - componentLaplacian C φ z := by
      simp only [componentLaplacian, hf, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [this, hharm z hzR hall, h1, sub_zero]
  have hfab : f a - f b = h 0 - h w := by
    simp only [hf, hu', hconst a b]
    ring
  have hl := hloc a b r hr2 f hab hharmf
  rw [hfab] at hl
  have hsub : componentEuclideanBall C a.val (4 * r) ⊆ componentEuclideanBall C 0 (5 * r) := by
    intro x hx
    rw [mem_componentEuclideanBall] at hx ⊢
    rw [show a.val = 0 from rfl] at hx
    linarith
  have hne : (componentEuclideanBall C a.val (4 * r)).Nonempty :=
    ⟨a, by rw [mem_componentEuclideanBall, dist_self]; linarith⟩
  have hball := sq_componentBallL2_le_of_subset C f hsub hne
  have hcard : ((componentEuclideanBall C 0 (5 * r)).card : ℝ) ≤ (12 * r) ^ d := by
    have h1 := componentEuclideanBall_card_le_box C 0 (5 * r)
    have hceil := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 5 * r by linarith)
    have h2 : 2 * (⌈5 * r⌉₊ : ℝ) + 1 ≤ 12 * r := by linarith
    exact h1.trans (pow_le_pow_left₀ (by positivity) h2 d)
  have hreg := hbd (5 * r) (by linarith) (by linarith)
  have hreg' : componentBallL2 C 0 (5 * r) f ≤ 15 * C₀ * r := by
    refine hreg.trans ?_
    calc C₀ * (5 * r / R) * componentBallL2 C 0 R u ≤ C₀ * (5 * r / R) * (3 * R) :=
          mul_le_mul_of_nonneg_left hsup (by positivity)
      _ = 15 * C₀ * r * (R / R) := by ring
      _ = 15 * C₀ * r := by rw [div_self hR0.ne', mul_one]
  have hstep : (h 0 - h w) ^ 2 ≤ (15 * 12 ^ d * Real.sqrt K * C₀ * r ^ d) ^ 2 := by
    have hl0 := componentBallL2_nonneg C 0 (5 * r) f
    have hrd : r ^ (d - 2) * r ^ d * r ^ 2 = r ^ d * r ^ d := by
      rw [mul_comm (r ^ (d - 2)), mul_assoc, ← pow_add, Nat.sub_add_cancel hd]
    have h12 : (12 : ℝ) ^ d ≤ 12 ^ d * 12 ^ d :=
      le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))
    calc (h 0 - h w) ^ 2 ≤ K * r ^ (d - 2) * componentBallL2 C a.val (4 * r) f ^ 2 := hl
      _ ≤ K * r ^ (d - 2) * (((componentEuclideanBall C 0 (5 * r)).card : ℝ) *
            componentBallL2 C 0 (5 * r) f ^ 2) :=
          mul_le_mul_of_nonneg_left hball (by positivity)
      _ ≤ K * r ^ (d - 2) * ((12 * r) ^ d * (15 * C₀ * r) ^ 2) := by
          gcongr
      _ = 12 ^ d * (K * 225 * C₀ ^ 2 * (r ^ (d - 2) * r ^ d * r ^ 2)) := by
          rw [mul_pow]
          ring
      _ ≤ (12 ^ d * 12 ^ d) * (K * 225 * C₀ ^ 2 * (r ^ (d - 2) * r ^ d * r ^ 2)) :=
          mul_le_mul_of_nonneg_right h12 (by positivity)
      _ = (15 * 12 ^ d * Real.sqrt K * C₀ * r ^ d) ^ 2 := by
          have hsq : Real.sqrt K ^ 2 = K := Real.sq_sqrt hK.le
          rw [hrd]
          simp only [mul_pow, hsq]
          ring
  have hpos : 0 ≤ 15 * 12 ^ d * Real.sqrt K * C₀ * r ^ d := by positivity
  have := sq_le_sq.1 hstep
  rwa [abs_of_nonneg hpos] at this

/-- **The local gradient bound through the minimal scale**: almost surely, for every `R ≥ 1`,
`localGrad R ω ≤ L max(X, 2)^d + 6R 1{the origin is in a finite cluster of at least R + 1
points}`. -/
theorem ae_localGrad_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∃ (L s θ : ℝ) (X : Configuration d → ℝ), 0 < L ∧ 0 < s ∧ 0 < θ ∧ Measurable X ∧
      (∀ ω, 0 ≤ X ω) ∧ IsOsBond d p X s θ ∧
      ∀ᵐ ω ∂latticeBondLaw d p, ∀ R : ℕ, 1 ≤ R →
        localGrad R ω ≤ L * max (X ω) 2 ^ d + 6 * R *
          (if {y | (openGraph ω).Reachable 0 y}.Finite ∧
            R + 1 ≤ {y | (openGraph ω).Reachable 0 y}.ncard then 1 else 0) := by
  obtain ⟨s, θ, C₀, hs, hθ, hC₀, X, hXm, hX0, hXi, hXb, hae⟩ :=
    Rigidity.Proofs.Regularity.armstrongDarioOrderZero_holds d hd p hpc hp1
  obtain ⟨K, hK, hloc⟩ := component_local_gradient d hd
  set L := max (15 * 12 ^ d * Real.sqrt K * C₀) 30 with hL
  refine ⟨L, s, θ, X, by positivity, hs, hθ, hXm, hX0, ?_, ?_⟩
  · have e : ∀ ω, max (X ω / θ) 0 = X ω / θ := fun ω => max_eq_left (div_nonneg (hX0 ω) hθ.le)
    unfold IsOsBond
    simp only [e]
    exact ⟨hXi, hXb⟩
  filter_upwards [hae] with ω hω R hR
  obtain ⟨hu, hall⟩ := hω
  obtain ⟨-, hfin, hH⟩ := hall hu
  have hm2 : (2 : ℝ) ≤ max (X ω) 2 := le_max_right _ _
  have hJ6 := localGrad_le ω hR
  have hLm : 0 ≤ L * max (X ω) 2 ^ d := by positivity
  have h6 : (0 : ℝ) ≤ 6 * R * (if {y | (openGraph ω).Reachable 0 y}.Finite ∧
      R + 1 ≤ {y | (openGraph ω).Reachable 0 y}.ncard then 1 else 0) := by
    positivity
  by_cases h0L : (0 : Vertex d) ∈ localCluster R ω
  · by_cases h0 : ω ∈ infiniteComponentEvent 0
    · have h0C := (mem_uniqueInfiniteComponent_iff hu 0).2 h0
      by_cases hR10 : 10 * max (X ω) 2 ≤ R
      · have hb := localGrad_le_of_orderZero hd hu hC₀ hK hfin hH
          (fun x y m hm f hxy hf => hloc ω _ x y m hm f hxy hf) h0C hR10
        have : 15 * 12 ^ d * Real.sqrt K * C₀ * max (X ω) 2 ^ d ≤ L * max (X ω) 2 ^ d :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
        linarith
      · rw [not_le] at hR10
        have h1 : (6 : ℝ) * R ≤ 30 * max (X ω) 2 ^ 2 := by nlinarith
        have h2 : max (X ω) 2 ^ 2 ≤ max (X ω) 2 ^ d := pow_le_pow_right₀ (by linarith) hd
        have h3 : 30 * max (X ω) 2 ^ d ≤ L * max (X ω) 2 ^ d :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
        linarith
    · have hsuppE : ((openGraph ω).connectedComponentMk 0).supp =
          {y | (openGraph ω).Reachable 0 y} := by
        ext y'
        rw [SimpleGraph.ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq]
        exact ⟨fun h => h.symm, fun h => h.symm⟩
      have hfinite : {y | (openGraph ω).Reachable 0 y}.Finite := by
        rw [← hsuppE]
        exact Set.not_infinite.1 h0
      obtain ⟨-, p', -, ⟨k, hk⟩, W, -⟩ := Finset.mem_filter.1 h0L
      have hdist : (R : ℤ) ≤ |p' k - (0 : Vertex d) k| := by
        simp only [Pi.zero_apply, sub_zero]
        push_cast at hk
        omega
      have hcard := le_card_support_of_walk W k hdist
      have hsupp : (W.support.toFinset : Set (Vertex d)) ⊆ {y | (openGraph ω).Reachable 0 y} :=
        fun v hv => (W.takeUntil v (List.mem_toFinset.1 (Finset.mem_coe.1 hv))).reachable
      have hn := Set.ncard_le_ncard hsupp hfinite
      rw [Set.ncard_coe_finset] at hn
      rw [if_pos ⟨hfinite, by omega⟩, mul_one]
      linarith
  · rw [localGrad_eq_zero_of_not_mem hR h0L]
    positivity

/-- The second term of the moments of the local gradient bound on `ℤᵈ`:
`(6R)^q C exp(-c (R + 1)^{1/d}) ≤ (6 (d/c)^d (C + 1) q^d)^q`. -/
theorem localGrad_term_two_le {R c C q : ℝ} (hd : 1 ≤ d) (hR : 1 ≤ R) (hc : 0 < c)
    (hC : 0 < C) (hq : 1 ≤ q) :
    (6 * R) ^ q * (C * Real.exp (-(c * (R + 1) ^ (d : ℝ)⁻¹))) ≤
      (6 * ((d : ℝ) / c) ^ d * (C + 1) * q ^ (d : ℝ)) ^ q := by
  have hq0 : 0 < q := by linarith
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  set x : ℝ := (R + 1) ^ (d : ℝ)⁻¹ with hx
  have hx0 : 0 ≤ x := by positivity
  have hxd : x ^ ((d : ℝ) * q) = (R + 1) ^ q := by
    rw [hx, ← Real.rpow_mul (by linarith), ← mul_assoc, inv_mul_cancel₀ hd0.ne', one_mul]
  have hRq : R ^ q ≤ (R + 1) ^ q := Real.rpow_le_rpow (by linarith) (by linarith) hq0.le
  have hkey := rpow_mul_exp_neg_le hx0 (by positivity : (0 : ℝ) < d * q) hc
  have hC1 : C ≤ (C + 1) ^ q := by
    calc C ≤ C + 1 := by linarith
      _ = (C + 1) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (C + 1) ^ q := Real.rpow_le_rpow_of_exponent_le (by linarith) hq
  have h2q : ((d : ℝ) * q / c) ^ ((d : ℝ) * q) = (((d : ℝ) / c) ^ d * q ^ (d : ℝ)) ^ q := by
    rw [Real.rpow_mul (by positivity)]
    congr 1
    rw [show (d : ℝ) * q / c = (d / c) * q by ring, Real.mul_rpow (by positivity) hq0.le,
      Real.rpow_natCast ((d : ℝ) / c) d]
  calc (6 * R) ^ q * (C * Real.exp (-(c * x)))
      = 6 ^ q * C * (R ^ q * Real.exp (-(c * x))) := by
        rw [Real.mul_rpow (by norm_num) (by linarith)]
        ring
    _ ≤ 6 ^ q * (C + 1) ^ q * (x ^ ((d : ℝ) * q) * Real.exp (-(c * x))) := by
        rw [hxd]
        gcongr
    _ ≤ 6 ^ q * (C + 1) ^ q * (((d : ℝ) / c) ^ d * q ^ (d : ℝ)) ^ q := by
        rw [← h2q]
        gcongr
    _ = (6 * ((d : ℝ) / c) ^ d * (C + 1) * q ^ (d : ℝ)) ^ q := by
        rw [← Real.mul_rpow (by norm_num) (by positivity),
          ← Real.mul_rpow (by positivity) (by positivity)]
        ring_nf

/-- **The moments of the local gradient bound, uniformly in the scale**, for `d ≥ 3`. -/
theorem growthMoments_localGrad [NeZero d] (hd : 3 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∃ B κ : ℝ, 0 < B ∧ 0 < κ ∧ ∀ R : ℕ, 1 ≤ R →
      GrowthMomentsD (d := d) p (fun ω => ENNReal.ofReal (1 + localGrad R ω)) B κ := by
  obtain ⟨L, s, θ, X, hL, hs, hθ, hXm, hX0, hXO, hae⟩ := ae_localGrad_le (by omega) hpc hp1
  obtain ⟨C₁, c₁, hC₁, hc₁, htail⟩ := exists_finite_cluster_card_le hd hpc
  set θ₂ : ℝ := max θ (2 * 3 ^ (1 / s)) * 4 ^ (1 / s) with hθ₂
  have hθ₂0 : 0 < θ₂ := by positivity
  have hX2 : IsOsBond d p (fun ω => max (X ω) 2) s θ₂ :=
    Rigidity.Proofs.S2.IsOsBond.max hs hθ (by positivity) hXm measurable_const hXO
      (Rigidity.Proofs.S2.isOsBond_const (by norm_num) hs)
  have hM := growthMomentsD_of_isOsBond (p := p)
    (fun ω => le_trans (by norm_num : (0 : ℝ) ≤ 2) (le_max_right (X ω) 2)) hs hθ₂0 hX2
  set B₀ : ℝ := 2 * θ₂ * (1 / s) ^ (1 / s) with hB₀
  have hB₀0 : 0 ≤ B₀ := by positivity
  have hY₁ := (hM.pow_nat hB₀0 d (by omega)).const_mul (c := L + 1) (by positivity)
    (by positivity)
  set B₁ : ℝ := (L + 1) * (B₀ ^ d * (d : ℝ) ^ (d * (1 / s))) with hB₁
  set A₂ : ℝ := 6 * ((d : ℝ) / c₁) ^ d * (C₁ + 1) with hA₂
  have hB₁0 : 0 ≤ B₁ := by positivity
  have hA₂0 : 0 < A₂ := by positivity
  refine ⟨2 * max B₁ A₂, max (d * (1 / s)) d, mul_pos two_pos (lt_max_of_lt_right hA₂0),
    lt_max_of_lt_right (by exact_mod_cast (show 0 < d by omega)), fun R hR => ?_⟩
  have hR' : (1 : ℝ) ≤ R := by exact_mod_cast hR
  set bad : Set (Configuration d) := {ω | {y | (openGraph ω).Reachable 0 y}.Finite ∧
    R + 1 ≤ {y | (openGraph ω).Reachable 0 y}.ncard} with hbad
  have hμbad : latticeBondLaw d p bad ≤
      ENNReal.ofReal (C₁ * Real.exp (-(c₁ * ((R : ℝ) + 1) ^ (d : ℝ)⁻¹))) := by
    have := htail 0 (R + 1)
    push_cast at this
    exact this
  have hY₂ : GrowthMomentsD p (fun ω => ENNReal.ofReal (6 * R) * bad.indicator 1 ω) A₂ d := by
    intro q hq
    have hq0 : 0 < q := by linarith
    have e : (fun ω => (ENNReal.ofReal (6 * R) * bad.indicator 1 ω) ^ q) =
        bad.indicator fun _ => ENNReal.ofReal ((6 * R) ^ q) := by
      funext ω
      by_cases hb : ω ∈ bad
      · rw [Set.indicator_of_mem hb, Set.indicator_of_mem hb, Pi.one_apply, mul_one,
          ENNReal.ofReal_rpow_of_nonneg (by positivity) hq0.le]
      · rw [Set.indicator_of_notMem hb, Set.indicator_of_notMem hb, mul_zero,
          ENNReal.zero_rpow_of_pos hq0]
    rw [e]
    refine (lintegral_indicator_const_le bad _).trans ?_
    refine (mul_le_mul_right hμbad _).trans ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal
      (GeneralDim.localGrad_term_two_le (by omega) hR' hc₁ hC₁ hq)
  have hY₁' := hY₁.of_le hB₁0 (le_max_left B₁ A₂) (le_max_left (d * (1 / s)) (d : ℝ))
  have hY₂' := hY₂.of_le hA₂0.le (le_max_right B₁ A₂) (le_max_right (d * (1 / s)) (d : ℝ))
  have hmeas : AEMeasurable (fun ω => ENNReal.ofReal (L + 1) *
      ENNReal.ofReal (max (X ω) 2) ^ (d : ℝ)) (latticeBondLaw d p) :=
    (((hXm.max measurable_const).ennreal_ofReal.pow_const _).const_mul _).aemeasurable
  have hsum := hY₁'.add hmeas hY₂' (le_max_of_le_right hA₂0.le)
  have hle : ∀ᵐ ω ∂latticeBondLaw d p, ENNReal.ofReal (1 + localGrad R ω) ≤
      ENNReal.ofReal (L + 1) * ENNReal.ofReal (max (X ω) 2) ^ (d : ℝ) +
        ENNReal.ofReal (6 * R) * bad.indicator 1 ω := by
    filter_upwards [hae] with ω hω
    have hJ := hω R hR
    set M := max (X ω) 2 with hMdef
    have hM2 : (2 : ℝ) ≤ M := le_max_right _ _
    have hM1 : (1 : ℝ) ≤ M ^ d := one_le_pow₀ (by linarith)
    set ind : ℝ := if {y | (openGraph ω).Reachable 0 y}.Finite ∧
      R + 1 ≤ {y | (openGraph ω).Reachable 0 y}.ncard then 1 else 0 with hind
    have hind0 : 0 ≤ ind := by rw [hind]; split_ifs <;> norm_num
    have hJ0 := localGrad_nonneg ω hR
    have e1 : ENNReal.ofReal (L + 1) * ENNReal.ofReal M ^ (d : ℝ) =
        ENNReal.ofReal ((L + 1) * M ^ d) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by linarith) (Nat.cast_nonneg d), Real.rpow_natCast,
        ← ENNReal.ofReal_mul (by linarith)]
    have e2 : ENNReal.ofReal (6 * R) * bad.indicator 1 ω = ENNReal.ofReal (6 * R * ind) := by
      rw [hind]
      by_cases hb : ω ∈ bad
      · rw [if_pos (show {y | (openGraph ω).Reachable 0 y}.Finite ∧
            R + 1 ≤ {y | (openGraph ω).Reachable 0 y}.ncard from hb),
          Set.indicator_of_mem hb, Pi.one_apply, mul_one, mul_one]
      · rw [if_neg (show ¬ ({y | (openGraph ω).Reachable 0 y}.Finite ∧
            R + 1 ≤ {y | (openGraph ω).Reachable 0 y}.ncard) from hb),
          Set.indicator_of_notMem hb, mul_zero, mul_zero, ENNReal.ofReal_zero]
    rw [e1, e2, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    nlinarith
  exact hsum.mono_ae hle

end Rigidity.Corrector.GeneralDim
