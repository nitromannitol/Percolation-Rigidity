import Rigidity.Proofs.Corrector.DarioLocalGradientProb
import Rigidity.Proofs.Corrector.DarioStepOneW

/-!
# Moments of the local gradient bound

On the event of the order-zero regularity (Armstrong and Dario, Theorem 2 (iii) at `k = 0`, with a
minimal scale `X`), every admissible function at scale `R ≥ 10 max(X, 2)` is harmonic on the cluster
in the ball of radius `R` and within `3R` of a constant there, so it is approximated on the ball of
radius `5 max(X, 2)` by a constant up to `15 C₀ max(X, 2)`, and the local gradient bound of the
cluster (`component_local_gradient`) bounds it along the edges at the origin by
`180 √K C₀ max(X, 2)²` (`localGrad_le_of_orderZero`, the argument of `abs_sub_le_of_orderZero` for
a function harmonic in a ball). When `R < 10 max(X, 2)` the bound `localGrad ≤ 6R` gives the same
form, and when the origin is in the local cluster but not in the infinite cluster it lies in a
finite cluster of at least `R + 1` points. Hence (`localGrad_le_max_sq`)

`localGrad R ω ≤ L max(X, 2)² + 6R 1{the origin is in a finite cluster of at least R + 1 points}`,

whose moments are bounded uniformly in `R` (`growthMoments_localGrad`).
-/

namespace Rigidity.Corrector

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.Proofs.Cluster
  Rigidity.Proofs.Section5 Rigidity.Poincare Rigidity.External
open scoped Classical ENNReal

theorem localGrad_eq_zero_of_not_mem {ω : Configuration 2} {R : ℕ} (hR : 1 ≤ R)
    (h0 : (0 : Vertex 2) ∉ localCluster R ω) : localGrad R ω = 0 := by
  refine le_antisymm (csSup_le (Set.insert_nonempty _ _) fun t ht => ?_)
    (localGrad_nonneg ω hR)
  rcases ht with rfl | ⟨_, _, _, h0', _, _⟩
  · exact le_rfl
  · exact absurd h0' h0

theorem mem_supBox_of_norm_le {x : Vertex 2} {R : ℕ}
    (h : ‖latticeEuclideanEmbedding x‖ ≤ R) : x ∈ supBox (0 : Vertex 2) R := by
  rw [mem_supBox]
  intro i
  have := (abs_coord_le_norm x i).trans h
  simp only [Pi.zero_apply, sub_zero]
  exact_mod_cast this

/-- **The local gradient bound through the order-zero regularity** (deterministic). -/
theorem localGrad_le_of_orderZero {ω : Configuration 2} (hu : HasUniqueInfiniteOpenComponent ω)
    {X₀ C₀ K : ℝ} (hC₀ : 0 < C₀) (hK : 0 < K)
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
      (f x - f y) ^ 2 ≤ K * m ^ (2 - 2) *
        (componentBallL2 (uniqueInfiniteComponent hu) x.val (4 * m) f) ^ 2)
    (h0 : (0 : Vertex 2) ∈ (uniqueInfiniteComponent hu).supp) {R : ℕ}
    (hR : 10 * max X₀ 2 ≤ R) :
    localGrad R ω ≤ 180 * Real.sqrt K * C₀ * max X₀ 2 ^ 2 := by
  set C := uniqueInfiniteComponent hu with hCdef
  set r : ℝ := max X₀ 2 with hr
  have hr2 : 2 ≤ r := le_max_right _ _
  have hXr : X₀ ≤ r := le_max_left _ _
  have hR1 : 1 ≤ R := by
    have : (1 : ℝ) ≤ R := by linarith
    exact_mod_cast this
  have hR0 : (0 : ℝ) < R := by linarith
  have hmemC : ∀ y, ω ∈ infiniteComponentEvent y → y ∈ C.supp := fun y hy =>
    (mem_uniqueInfiniteComponent_iff hu y).2 hy
  have hICE : ∀ y ∈ C.supp, ω ∈ infiniteComponentEvent y := fun y hy =>
    (mem_uniqueInfiniteComponent_iff hu y).1 hy
  refine csSup_le (Set.insert_nonempty _ _) fun t ht => ?_
  rcases ht with rfl | ⟨h, w, ⟨hharmh, c, hc⟩, h0L, hw, rfl⟩
  · positivity
  set u : C → ℝ := fun x => h x.val - c with hu'
  -- the admissible function is harmonic on the cluster in the ball of radius `R`
  have hharm : ∀ x ∈ componentEuclideanBall C 0 R,
      (∀ y : C, (componentGraph C).Adj x y → y ∈ componentEuclideanBall C 0 R) →
        componentLaplacian C u x = 0 := by
    intro x hx hall
    have hxR := (mem_componentEuclideanBall C 0 R x).1 hx
    rw [dist_eq_norm, latticeEuclideanEmbedding_zero, sub_zero] at hxR
    have hxB := mem_supBox_of_norm_le (R := R) hxR.le
    have hxL := mem_localCluster_of_infinite hxB (hICE x.val x.2)
    have hlap : openLaplacian ω h x.val = 0 := by
      refine hharmh x.val hxL fun w' hw' => ?_
      have hw'C : w' ∈ C.supp := C.mem_supp_of_adj_mem_supp x.2 hw'
      have hadj : (componentGraph C).Adj x ⟨w', hw'C⟩ := (C.toSimpleGraph_adj x.2 hw'C).2 hw'
      have hy := (mem_componentEuclideanBall C 0 R _).1 (hall _ hadj)
      rw [dist_eq_norm, latticeEuclideanEmbedding_zero, sub_zero] at hy
      exact mem_supBox_of_norm_le hy.le
    have e : componentLaplacian C u x = componentLaplacian C (fun y => h y.val) x := by
      simp only [componentLaplacian, hu', sub_sub_sub_cancel_right]
    rw [e, componentLaplacian_restrict_eq C h x]
    exact hlap
  have hsup : componentBallL2 C 0 R u ≤ 3 * R := by
    refine componentBallL2_le_of_abs_le C 0 R u (by positivity) fun x hx => ?_
    have hxR := (mem_componentEuclideanBall C 0 R x).1 hx
    rw [dist_eq_norm, latticeEuclideanEmbedding_zero, sub_zero] at hxR
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
    rw [dist_eq_norm, show a.val = 0 from rfl, latticeEuclideanEmbedding_zero, sub_zero] at hz'
    have hzR : z ∈ componentEuclideanBall C 0 R := by
      rw [mem_componentEuclideanBall, dist_eq_norm, latticeEuclideanEmbedding_zero, sub_zero]
      linarith
    have hall : ∀ y : C, (componentGraph C).Adj z y → y ∈ componentEuclideanBall C 0 R := by
      intro y hy
      rw [mem_componentEuclideanBall, dist_eq_norm, latticeEuclideanEmbedding_zero, sub_zero]
      have hadj := (C.toSimpleGraph_adj z.2 y.2).1 hy
      have h1y : ‖latticeEuclideanEmbedding y.val‖ ≤ ‖latticeEuclideanEmbedding z.val‖ + 2 := by
        have e : latticeEuclideanEmbedding y.val = latticeEuclideanEmbedding z.val +
            (latticeEuclideanEmbedding y.val - latticeEuclideanEmbedding z.val) := by abel
        rw [e]
        refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
        have hn := norm_latticeEuclideanEmbedding_le_sum (y.val - z.val)
        have e2 : latticeEuclideanEmbedding (y.val - z.val) =
            latticeEuclideanEmbedding y.val - latticeEuclideanEmbedding z.val := by
          ext k; simp [latticeEuclideanEmbedding]
        rw [← e2]
        refine hn.trans ?_
        have h0' := abs_sub_le_one_of_adj hadj 0
        have h1' := abs_sub_le_one_of_adj hadj 1
        rw [abs_sub_comm] at h0' h1'
        simp only [Pi.sub_apply, Int.cast_sub]
        linarith
      linarith
    have : componentLaplacian C f z = componentLaplacian C u z - componentLaplacian C φ z := by
      simp only [componentLaplacian, hf, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [this, hharm z hzR hall, h1, sub_zero]
  have hfab : f a - f b = h 0 - h w := by
    simp only [hf, hu', hconst a b]
    ring
  have hl := hloc a b r hr2 f hab hharmf
  rw [hfab, show (2 - 2 : ℕ) = 0 by norm_num, pow_zero, mul_one] at hl
  have hsub : componentEuclideanBall C a.val (4 * r) ⊆ componentEuclideanBall C 0 (5 * r) := by
    intro x hx
    rw [mem_componentEuclideanBall] at hx ⊢
    rw [show a.val = 0 from rfl] at hx
    linarith
  have hne : (componentEuclideanBall C a.val (4 * r)).Nonempty :=
    ⟨a, by rw [mem_componentEuclideanBall, dist_self]; linarith⟩
  have hball := sq_componentBallL2_le_of_subset C f hsub hne
  have hcard : ((componentEuclideanBall C 0 (5 * r)).card : ℝ) ≤ (12 * r) ^ 2 := by
    have h1 := componentEuclideanBall_card_le_box C 0 (5 * r)
    have hceil := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 5 * r by linarith)
    have h2 : 2 * (⌈5 * r⌉₊ : ℝ) + 1 ≤ 12 * r := by linarith
    exact h1.trans (pow_le_pow_left₀ (by positivity) h2 2)
  have hreg := hbd (5 * r) (by linarith) (by linarith)
  have hreg' : componentBallL2 C 0 (5 * r) f ≤ 15 * C₀ * r := by
    refine hreg.trans ?_
    calc C₀ * (5 * r / R) * componentBallL2 C 0 R u ≤ C₀ * (5 * r / R) * (3 * R) :=
          mul_le_mul_of_nonneg_left hsup (by positivity)
      _ = 15 * C₀ * r * (R / R) := by ring
      _ = 15 * C₀ * r := by rw [div_self hR0.ne', mul_one]
  have hstep : (h 0 - h w) ^ 2 ≤ (180 * Real.sqrt K * C₀ * r ^ 2) ^ 2 := by
    have hl0 := componentBallL2_nonneg C 0 (5 * r) f
    calc (h 0 - h w) ^ 2 ≤ K * componentBallL2 C a.val (4 * r) f ^ 2 := hl
      _ ≤ K * (((componentEuclideanBall C 0 (5 * r)).card : ℝ) *
            componentBallL2 C 0 (5 * r) f ^ 2) := mul_le_mul_of_nonneg_left hball hK.le
      _ ≤ K * ((12 * r) ^ 2 * (15 * C₀ * r) ^ 2) := by
          gcongr
      _ = (180 * Real.sqrt K * C₀ * r ^ 2) ^ 2 := by
          have hsq : Real.sqrt K ^ 2 = K := Real.sq_sqrt hK.le
          simp only [mul_pow, hsq]
          ring
  have hpos : 0 ≤ 180 * Real.sqrt K * C₀ * r ^ 2 := by positivity
  have := sq_le_sq.1 hstep
  rwa [abs_of_nonneg hpos] at this


/-- `x^a e^{-c x} ≤ (a / c)^a` for `x, a ≥ 0`, `c > 0`. -/
theorem rpow_mul_exp_neg_le {x a c : ℝ} (hx : 0 ≤ x) (ha : 0 < a) (hc : 0 < c) :
    x ^ a * Real.exp (-(c * x)) ≤ (a / c) ^ a := by
  have h1 : c * x / a ≤ Real.exp (c * x / a) := by
    have := Real.add_one_le_exp (c * x / a)
    linarith
  have h2 : (c * x / a) ^ a ≤ Real.exp (c * x) := by
    calc (c * x / a) ^ a ≤ Real.exp (c * x / a) ^ a :=
          Real.rpow_le_rpow (by positivity) h1 ha.le
      _ = Real.exp (c * x) := by
          rw [← Real.exp_mul]; congr 1; field_simp
  have h3 : x ^ a = (a / c) ^ a * (c * x / a) ^ a := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    field_simp
  rw [h3, mul_assoc]
  have h4 : (c * x / a) ^ a * Real.exp (-(c * x)) ≤ 1 := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
    exact h2
  calc (a / c) ^ a * ((c * x / a) ^ a * Real.exp (-(c * x))) ≤ (a / c) ^ a * 1 :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = (a / c) ^ a := mul_one _

/-- **The local gradient bound through the minimal scale**: almost surely, for every `R ≥ 1`,
`localGrad R ω ≤ L max(X, 2)² + 6R 1{the origin is in a finite cluster of at least R + 1
points}`. -/
theorem ae_localGrad_le {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) :
    ∃ (L s θ : ℝ) (X : Configuration 2 → ℝ), 0 < L ∧ 0 < s ∧ 0 < θ ∧ Measurable X ∧
      (∀ ω, 0 ≤ X ω) ∧ IsOsBond 2 p X s θ ∧
      ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ R : ℕ, 1 ≤ R →
        localGrad R ω ≤ L * max (X ω) 2 ^ 2 + 6 * R *
          (if ((openGraph ω).connectedComponentMk 0).supp.Finite ∧
            R + 1 ≤ ((openGraph ω).connectedComponentMk 0).supp.ncard then 1 else 0) := by
  obtain ⟨s, θ, C₀, hs, hθ, hC₀, X, hXm, hX0, hXi, hXb, hae⟩ :=
    Rigidity.Proofs.Regularity.armstrongDarioOrderZeroTwo_holds p hpc hp1
  obtain ⟨K, hK, hloc⟩ := component_local_gradient 2 le_rfl
  set L := max (180 * Real.sqrt K * C₀) 30 with hL
  refine ⟨L, s, θ, X, by positivity, hs, hθ, hXm, hX0, ?_, ?_⟩
  · have e : ∀ ω, max (X ω / θ) 0 = X ω / θ := fun ω => max_eq_left (div_nonneg (hX0 ω) hθ.le)
    unfold IsOsBond
    simp only [e]
    exact ⟨hXi, hXb⟩
  filter_upwards [hae] with ω hω R hR
  obtain ⟨hu, hall⟩ := hω
  obtain ⟨-, hfin, hH⟩ := hall hu
  have hm2 : (2 : ℝ) ≤ max (X ω) 2 := le_max_right _ _
  have hJ0 := localGrad_nonneg ω hR
  have hJ6 := localGrad_le ω hR
  have hind0 : (0 : ℝ) ≤ (if ((openGraph ω).connectedComponentMk 0).supp.Finite ∧
      R + 1 ≤ ((openGraph ω).connectedComponentMk 0).supp.ncard then 1 else 0) := by
    split_ifs <;> norm_num
  have hLm : 0 ≤ L * max (X ω) 2 ^ 2 := by positivity
  by_cases h0L : (0 : Vertex 2) ∈ localCluster R ω
  · by_cases h0 : ω ∈ infiniteComponentEvent 0
    · have h0C := (mem_uniqueInfiniteComponent_iff hu 0).2 h0
      by_cases hR10 : 10 * max (X ω) 2 ≤ R
      · have hb := localGrad_le_of_orderZero hu hC₀ hK hfin hH
          (fun x y m hm f hxy hf => hloc ω _ x y m hm f hxy hf) h0C hR10
        have : 180 * Real.sqrt K * C₀ * max (X ω) 2 ^ 2 ≤ L * max (X ω) 2 ^ 2 :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
        have h6 : (0 : ℝ) ≤ 6 * R * (if ((openGraph ω).connectedComponentMk 0).supp.Finite ∧
            R + 1 ≤ ((openGraph ω).connectedComponentMk 0).supp.ncard then 1 else 0) := by
          positivity
        linarith
      · rw [not_le] at hR10
        have h1 : (6 : ℝ) * R ≤ 30 * max (X ω) 2 ^ 2 := by nlinarith
        have h2 : 30 * max (X ω) 2 ^ 2 ≤ L * max (X ω) 2 ^ 2 :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)
        have h6 : (0 : ℝ) ≤ 6 * R * (if ((openGraph ω).connectedComponentMk 0).supp.Finite ∧
            R + 1 ≤ ((openGraph ω).connectedComponentMk 0).supp.ncard then 1 else 0) := by
          positivity
        linarith
    · -- the origin is in a finite cluster of at least `R + 1` points
      have hfinite : ((openGraph ω).connectedComponentMk 0).supp.Finite := Set.not_infinite.1 h0
      obtain ⟨-, p', -, ⟨k, hk⟩, W, -⟩ := Finset.mem_filter.1 h0L
      have hdist : (R : ℤ) ≤ |p' k - (0 : Vertex 2) k| := by
        simp only [Pi.zero_apply, sub_zero]
        push_cast at hk
        omega
      have hcard := le_card_support_of_walk W k hdist
      have hsupp : (W.support.toFinset : Set (Vertex 2)) ⊆
          ((openGraph ω).connectedComponentMk 0).supp := by
        intro v hv
        rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
        exact (SimpleGraph.ConnectedComponent.sound
          (W.takeUntil v (List.mem_toFinset.1 (Finset.mem_coe.1 hv))).reachable).symm
      have hn := Set.ncard_le_ncard hsupp hfinite
      rw [Set.ncard_coe_finset] at hn
      rw [if_pos ⟨hfinite, by omega⟩, mul_one]
      linarith
  · rw [localGrad_eq_zero_of_not_mem hR h0L]
    positivity


theorem rpow_le_rpow_of_one_le {q a b : ℝ} (hq : 1 ≤ q) (hab : a ≤ b) : q ^ a ≤ q ^ b :=
  Real.rpow_le_rpow_of_exponent_le hq hab

/-- The first term of the moments of the local gradient bound. -/
theorem localGrad_term_one_le {L D s q κ : ℝ} (hL : 0 < L) (hD : 0 < D)
    (hq : 1 ≤ q) (hκ : 4 / s ≤ κ) :
    (L + 1) ^ q * (3 * (2 * D * q ^ (1 / s)) ^ (4 * q)) ≤
      (3 * (L + 1) * (2 * D) ^ 4 * q ^ κ) ^ q := by
  have hq0 : 0 < q := by linarith
  have e1 : (2 * D * q ^ (1 / s)) ^ (4 * q) = ((2 * D) ^ 4 * q ^ (4 / s)) ^ q := by
    have := rpow_natCast_mul_eq (by positivity : 0 ≤ 2 * D * q ^ (1 / s)) 4 q
    simp only [Nat.cast_ofNat] at this
    rw [this, mul_pow, ← Real.rpow_natCast (q ^ (1 / s)) 4, ← Real.rpow_mul hq0.le]
    congr 3
    push_cast
    ring
  rw [e1]
  have h3 : (3 : ℝ) ≤ 3 ^ q := by
    calc (3 : ℝ) = 3 ^ (1 : ℝ) := (Real.rpow_one 3).symm
      _ ≤ 3 ^ q := Real.rpow_le_rpow_of_exponent_le (by norm_num) hq
  have hk : q ^ (4 / s) ≤ q ^ κ := rpow_le_rpow_of_one_le hq hκ
  calc (L + 1) ^ q * (3 * ((2 * D) ^ 4 * q ^ (4 / s)) ^ q)
      ≤ (L + 1) ^ q * (3 ^ q * ((2 * D) ^ 4 * q ^ κ) ^ q) := by
        gcongr
    _ = (3 * (L + 1) * (2 * D) ^ 4 * q ^ κ) ^ q := by
        rw [← Real.mul_rpow (by norm_num) (by positivity),
          ← Real.mul_rpow (by positivity) (by positivity)]
        ring_nf

/-- The second term of the moments of the local gradient bound. -/
theorem localGrad_term_two_le {R c C q κ : ℝ} (hR : 1 ≤ R) (hc : 0 < c) (hC : 0 < C)
    (hq : 1 ≤ q) (hκ : 2 ≤ κ) :
    (6 * R) ^ q * (C * Real.exp (-(c * Real.sqrt (R + 1)))) ≤
      (36 * (2 / c) ^ 2 * (C + 1) * q ^ κ) ^ q := by
  have hq0 : 0 < q := by linarith
  have hsR : 0 ≤ Real.sqrt R := Real.sqrt_nonneg R
  have hexp : Real.exp (-(c * Real.sqrt (R + 1))) ≤ Real.exp (-(c * Real.sqrt R)) := by
    refine Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left ?_ hc.le))
    exact Real.sqrt_le_sqrt (by linarith)
  have hRq : R ^ q = Real.sqrt R ^ (2 * q) := by
    rw [show (2 : ℝ) * q = ((2 : ℕ) : ℝ) * q by norm_num, rpow_natCast_mul_eq hsR,
      Real.sq_sqrt (by linarith)]
  have hkey := rpow_mul_exp_neg_le hsR (by positivity : (0 : ℝ) < 2 * q) hc
  have hC1 : C ≤ (C + 1) ^ q := by
    calc C ≤ C + 1 := by linarith
      _ = (C + 1) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (C + 1) ^ q := Real.rpow_le_rpow_of_exponent_le (by linarith) hq
  have h2q : (2 * q / c) ^ (2 * q) = ((2 / c) ^ 2 * q ^ 2) ^ q := by
    rw [show (2 : ℝ) * q = ((2 : ℕ) : ℝ) * q by norm_num, rpow_natCast_mul_eq (by positivity)]
    congr 1
    ring
  have hk : q ^ (2 : ℝ) ≤ q ^ κ := rpow_le_rpow_of_one_le hq hκ
  calc (6 * R) ^ q * (C * Real.exp (-(c * Real.sqrt (R + 1))))
      ≤ (6 * R) ^ q * (C * Real.exp (-(c * Real.sqrt R))) := by gcongr
    _ = 6 ^ q * C * (Real.sqrt R ^ (2 * q) * Real.exp (-(c * Real.sqrt R))) := by
        rw [Real.mul_rpow (by norm_num) (by linarith), hRq]; ring
    _ ≤ 6 ^ q * (C + 1) ^ q * ((2 / c) ^ 2 * q ^ 2) ^ q := by
        rw [← h2q]
        gcongr
    _ ≤ 6 ^ q * (C + 1) ^ q * ((2 / c) ^ 2 * q ^ κ) ^ q := by
        gcongr
        rw [← Real.rpow_natCast q 2]
        exact_mod_cast hk
    _ ≤ 36 ^ q * (C + 1) ^ q * ((2 / c) ^ 2 * q ^ κ) ^ q := by
        gcongr
        norm_num
    _ = (36 * (2 / c) ^ 2 * (C + 1) * q ^ κ) ^ q := by
        rw [← Real.mul_rpow (by norm_num) (by positivity),
          ← Real.mul_rpow (by positivity) (by positivity)]
        ring_nf

/-- Moments with polynomial growth: `E[Y^q] ≤ (B q^κ)^q` for every `q ≥ 1`. -/
def GrowthMoments (p : unitInterval) (Y : Configuration 2 → ℝ≥0∞) (B κ : ℝ) : Prop :=
  ∀ q : ℝ, 1 ≤ q → ∫⁻ ω, Y ω ^ q ∂latticeBondLaw 2 p ≤ ENNReal.ofReal ((B * q ^ κ) ^ q)

/-- **The moments of the local gradient bound, uniformly in the scale.** -/
theorem growthMoments_localGrad {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) :
    ∃ B κ : ℝ, 0 < B ∧ 0 < κ ∧ ∀ R : ℕ, 1 ≤ R →
      GrowthMoments p (fun ω => ENNReal.ofReal (1 + localGrad R ω)) B κ := by
  obtain ⟨L, s, θ, X, hL, hs, hθ, hXm, hX0, hXO, hae⟩ := ae_localGrad_le hpc hp1
  obtain ⟨C₁, c₁, hC₁, hc₁, htail⟩ := planar_finite_cluster_size_tail_at p hpc
  set D := θ * (4 / s) ^ (1 / s) + 2 with hD
  have hD0 : 0 < D := by positivity
  set A₁ := 3 * (L + 1) * (2 * D) ^ 4 with hA₁
  set A₂ := 36 * (2 / c₁) ^ 2 * (C₁ + 1) with hA₂
  have hA₁0 : 0 < A₁ := by positivity
  have hA₂0 : 0 < A₂ := by positivity
  set κ := max (4 / s) 2 with hκ
  refine ⟨2 * (A₁ + A₂), κ, by positivity, by positivity, fun R hR q hq => ?_⟩
  have hq0 : 0 < q := by linarith
  have hR' : (1 : ℝ) ≤ R := by exact_mod_cast hR
  set bad : Set (Configuration 2) := {ω | ((openGraph ω).connectedComponentMk 0).supp.Finite ∧
    R + 1 ≤ ((openGraph ω).connectedComponentMk 0).supp.ncard} with hbad
  have hμbad : latticeBondLaw 2 p bad ≤
      ENNReal.ofReal (C₁ * Real.exp (-(c₁ * Real.sqrt (R + 1)))) := by
    have := htail 0 (R + 1)
    push_cast at this
    exact this
  -- the pointwise bound
  set F : Configuration 2 → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal (2 ^ (q - 1) * (((L + 1) * (X ω + 2) ^ 2) ^ q)) with hF
  have hFm : Measurable F := by
    refine ENNReal.measurable_ofReal.comp (Measurable.const_mul ?_ _)
    exact (((hXm.add_const 2).pow_const 2).const_mul _).pow_const _
  have hpt : ∀ᵐ ω ∂latticeBondLaw 2 p, ENNReal.ofReal (1 + localGrad R ω) ^ q ≤
      F ω + ENNReal.ofReal (2 ^ (q - 1) * (6 * R) ^ q) * bad.indicator 1 ω := by
    filter_upwards [hae] with ω hω
    have hJ := hω R hR
    have hX2 : max (X ω) 2 ≤ X ω + 2 := max_le (by linarith [hX0 ω]) (by linarith [hX0 ω])
    have hm : max (X ω) 2 ^ 2 ≤ (X ω + 2) ^ 2 :=
      pow_le_pow_left₀ (le_max_of_le_right (by norm_num)) hX2 2
    have h1 : (1 : ℝ) ≤ (X ω + 2) ^ 2 := by nlinarith [hX0 ω]
    set ind : ℝ := if ((openGraph ω).connectedComponentMk 0).supp.Finite ∧
      R + 1 ≤ ((openGraph ω).connectedComponentMk 0).supp.ncard then 1 else 0 with hind
    have hind0 : 0 ≤ ind := by rw [hind]; split_ifs <;> norm_num
    have hbound : 1 + localGrad R ω ≤ (L + 1) * (X ω + 2) ^ 2 + 6 * R * ind := by
      nlinarith
    have hJ0 := localGrad_nonneg ω hR
    rw [ENNReal.ofReal_rpow_of_nonneg (by linarith) hq0.le]
    have hsplit := rpow_add_le_two_rpow (by positivity : (0 : ℝ) ≤ (L + 1) * (X ω + 2) ^ 2)
      (by positivity : (0 : ℝ) ≤ 6 * R * ind) hq
    have hmono := Real.rpow_le_rpow (by linarith) hbound hq0.le
    have hind_q : (6 * R * ind) ^ q = (6 * R) ^ q * ind := by
      rw [hind]
      split_ifs
      · rw [mul_one, mul_one]
      · rw [mul_zero, mul_zero, Real.zero_rpow hq0.ne']
    rw [hind_q] at hsplit
    calc ENNReal.ofReal ((1 + localGrad R ω) ^ q)
        ≤ ENNReal.ofReal (2 ^ (q - 1) * (((L + 1) * (X ω + 2) ^ 2) ^ q) +
            2 ^ (q - 1) * (6 * R) ^ q * ind) := by
          refine ENNReal.ofReal_le_ofReal (hmono.trans (hsplit.trans (le_of_eq ?_)))
          ring
      _ = F ω + ENNReal.ofReal (2 ^ (q - 1) * (6 * R) ^ q) * bad.indicator 1 ω := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          rw [hind]
          by_cases hb : ω ∈ bad
          · rw [if_pos (show ((openGraph ω).connectedComponentMk 0).supp.Finite ∧
                R + 1 ≤ ((openGraph ω).connectedComponentMk 0).supp.ncard from hb),
              Set.indicator_of_mem hb, Pi.one_apply, mul_one, mul_one]
          · rw [if_neg (show ¬ (((openGraph ω).connectedComponentMk 0).supp.Finite ∧
                R + 1 ≤ ((openGraph ω).connectedComponentMk 0).supp.ncard) from hb),
              Set.indicator_of_notMem hb, mul_zero, mul_zero, ENNReal.ofReal_zero]
  -- integrating
  have hint : ∫⁻ ω, ENNReal.ofReal (1 + localGrad R ω) ^ q ∂latticeBondLaw 2 p ≤
      ENNReal.ofReal (2 ^ (q - 1) * (L + 1) ^ q * (3 * (2 * D * q ^ (1 / s)) ^ (4 * q))) +
        ENNReal.ofReal (2 ^ (q - 1) * (6 * R) ^ q) *
          ENNReal.ofReal (C₁ * Real.exp (-(c₁ * Real.sqrt (R + 1)))) := by
    refine (lintegral_mono_ae hpt).trans ?_
    rw [lintegral_add_left hFm, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine add_le_add ?_ ?_
    swap
    · gcongr
      exact (lintegral_indicator_one_le bad).trans hμbad
    have hF' : ∀ ω, F ω ≤ ENNReal.ofReal (2 ^ (q - 1) * (L + 1) ^ q) *
        ENNReal.ofReal ((X ω + 2) ^ (4 * q)) := by
      intro ω
      simp only [hF]
      rw [← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hX1 : 1 ≤ X ω + 2 := by linarith [hX0 ω]
      rw [Real.mul_rpow (by positivity) (by positivity), mul_assoc]
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity))
        (by positivity)
      rw [← rpow_natCast_mul_eq (by linarith) 2 q]
      exact Real.rpow_le_rpow_of_exponent_le hX1 (by push_cast; linarith)
    refine (lintegral_mono hF').trans ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ENNReal.ofReal (2 ^ (q - 1) * (L + 1) ^ q) *
          ∫⁻ ω, ENNReal.ofReal ((X ω + 2) ^ (4 * q)) ∂latticeBondLaw 2 p
        ≤ ENNReal.ofReal (2 ^ (q - 1) * (L + 1) ^ q) *
          ENNReal.ofReal (3 * (2 * D * q ^ (1 / s)) ^ (4 * q)) := by
          gcongr
          exact lintegral_add_two_rpow_le hs hθ hXm hX0 hXO hq
      _ = ENNReal.ofReal (2 ^ (q - 1) * (L + 1) ^ q * (3 * (2 * D * q ^ (1 / s)) ^ (4 * q))) :=
          (ENNReal.ofReal_mul (by positivity)).symm
  refine hint.trans ?_
  have h1 := localGrad_term_one_le hL hD0 hq (le_max_left (4 / s) 2)
  have h2 := localGrad_term_two_le hR' hc₁ hC₁ hq (le_max_right (4 / s) 2)
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h2q : (0 : ℝ) ≤ 2 ^ (q - 1) := by positivity
  have hsum : (A₁ * q ^ κ) ^ q + (A₂ * q ^ κ) ^ q ≤ 2 * ((A₁ + A₂) * q ^ κ) ^ q := by
    have a1 : (A₁ * q ^ κ) ^ q ≤ ((A₁ + A₂) * q ^ κ) ^ q :=
      Real.rpow_le_rpow (by positivity) (by gcongr; linarith) (by linarith)
    have a2 : (A₂ * q ^ κ) ^ q ≤ ((A₁ + A₂) * q ^ κ) ^ q :=
      Real.rpow_le_rpow (by positivity) (by gcongr; linarith) (by linarith)
    linarith
  have h2pow : (2 : ℝ) ^ (q - 1) * 2 = 2 ^ q := by
    rw [← Real.rpow_add_one (by norm_num)]; ring_nf
  calc 2 ^ (q - 1) * (L + 1) ^ q * (3 * (2 * D * q ^ (1 / s)) ^ (4 * q)) +
        2 ^ (q - 1) * (6 * R) ^ q * (C₁ * Real.exp (-(c₁ * Real.sqrt (R + 1))))
      = 2 ^ (q - 1) * ((L + 1) ^ q * (3 * (2 * D * q ^ (1 / s)) ^ (4 * q)) +
        (6 * R) ^ q * (C₁ * Real.exp (-(c₁ * Real.sqrt (R + 1))))) := by ring
    _ ≤ 2 ^ (q - 1) * ((A₁ * q ^ κ) ^ q + (A₂ * q ^ κ) ^ q) := by gcongr
    _ ≤ 2 ^ (q - 1) * (2 * ((A₁ + A₂) * q ^ κ) ^ q) := by gcongr
    _ = 2 ^ q * ((A₁ + A₂) * q ^ κ) ^ q := by rw [← mul_assoc, h2pow]
    _ = (2 * (A₁ + A₂) * q ^ κ) ^ q := by
        rw [← Real.mul_rpow (by norm_num) (by positivity)]; ring_nf

end Rigidity.Corrector
