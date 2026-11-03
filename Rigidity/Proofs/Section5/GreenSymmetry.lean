import Rigidity.Proofs.Section5.FiniteMaxPrinciple
import Rigidity.Proofs.Section5.PotentialLimit
import Rigidity.Proofs.Section5.SublinearLiouville
import Rigidity.Steps.Section5.GradientTrichotomy
import LatticeProb.Prob.Percolation.LatticeRadialTail

/-!
# Symmetry of the normalized Green function

`GreenSymmetry p` (a step of the carving of Proposition 5.7, corrected draft L459):
almost surely, for every Green family `G` of `𝒞_∞` there is `κ` with
`G(x, y) - κ(y) = G(y, x) - κ(x)`. It is proved here from the asymptotics of the Green columns
(`PotentialAsymptotic p`, itself proved from the input `SupercriticalBondGreenQuantitative` for
`p_c < p < 1` in `PotentialLimit.lean`), with `κ(y) = K(y) = lim_{x → ∞} (G(x, y) - Ḡ(x))`.

Route (deterministic, `greenFamily_symm`). Let `S = 𝒞_∞ ∩ B_n` (finite) and let `h_y` be harmonic on
`S` with `h_y = G(·, y)` off `S` (Dirichlet problem: the Laplacian with zero boundary values is
injective by the finite maximum principle, hence invertible). Then `G_S(·, y) = G(·, y) - h_y`
vanishes off `S` with `-Δ G_S(·, y) = δ_y` on `S`, and `Σ_S φ Δψ` is symmetric in `φ, ψ` vanishing
off `S`, so `G_S(x, y) = G_S(y, x)` and `G(x, y) - G(y, x) = h_y(x) - h_x(y)`. On the outer boundary
of `S`, `n ≤ |w| < n + 1`, so `G(w, y) = Ḡ(n) + K(y) + O(ε + 1/n)`; the maximum principle gives
`h_y(x) = Ḡ(n) + K(y) + O(ε + 1/n)`, and `n → ∞` gives `G(x, y) - G(y, x) = K(y) - K(x)`.
-/

open MeasureTheory LatticeProb LatticeProb.Percolation Filter Topology

namespace Rigidity.Proofs.Section5

open Rigidity.Section5 Rigidity.Steps.Section5

variable {ω : Configuration 2}

/-- Nearest neighbours of `ℤ²` are at Euclidean distance at most one. -/
theorem norm_embedding_sub_le_one_of_adj {x y : Vertex 2} (h : (nearestNeighborGraph 2).Adj x y) :
    ‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding y‖ ≤ 1 := by
  have h1 : ((latticeL1Dist x y : ℤ) : ℝ) = 1 := by exact_mod_cast lattice_adj_iff_l1Dist.1 h
  rw [← latticeEuclideanEmbedding_sub, EuclideanSpace.norm_eq]
  have hc : ∀ j, ‖latticeEuclideanEmbedding (x - y) j‖ = |((x j - y j : ℤ) : ℝ)| := fun j => by
    rw [Real.norm_eq_abs]
    rfl
  have hsum : ∑ j, ‖latticeEuclideanEmbedding (x - y) j‖ = 1 := by
    rw [← h1, latticeL1Dist, Finset.sum_congr rfl fun j _ => hc j]
    push_cast
    rfl
  calc √(∑ j, ‖latticeEuclideanEmbedding (x - y) j‖ ^ 2)
      ≤ √((∑ j, ‖latticeEuclideanEmbedding (x - y) j‖) ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_sq_le_sq_sum_of_nonneg fun j _ => norm_nonneg _)
    _ = ∑ j, ‖latticeEuclideanEmbedding (x - y) j‖ :=
        Real.sqrt_sq (Finset.sum_nonneg fun j _ => norm_nonneg _)
    _ = 1 := hsum

section Dirichlet

variable (C : OpenComponent ω)

theorem componentLaplacian_add_fun (u v : C → ℝ) (x : C) :
    componentLaplacian C (fun y => u y + v y) x =
      componentLaplacian C u x + componentLaplacian C v x := by
  simp only [componentLaplacian, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun y _ => by ring

theorem componentLaplacian_sub_fun (u v : C → ℝ) (x : C) :
    componentLaplacian C (fun y => u y - v y) x =
      componentLaplacian C u x - componentLaplacian C v x := by
  simp only [componentLaplacian, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun y _ => by ring

theorem componentLaplacian_mul_fun (c : ℝ) (u : C → ℝ) (x : C) :
    componentLaplacian C (fun y => c * u y) x = c * componentLaplacian C u x := by
  simp only [componentLaplacian, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

theorem componentLaplacian_neg_fun (u : C → ℝ) (x : C) :
    componentLaplacian C (fun y => -u y) x = -componentLaplacian C u x := by
  simp only [componentLaplacian, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun y _ => by ring

/-- The Laplacian on a finite set `S` with zero boundary values, as a linear map. -/
noncomputable def dirichletLaplacian (S : Finset C) : (S → ℝ) →ₗ[ℝ] (S → ℝ) where
  toFun u z := componentLaplacian C (fun y => if hy : y ∈ S then u ⟨y, hy⟩ else 0) z.val
  map_add' u v := by
    funext z
    simp only [Pi.add_apply]
    rw [← componentLaplacian_add_fun]
    congr 1
    funext y
    split_ifs <;> simp
  map_smul' c u := by
    funext z
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [← componentLaplacian_mul_fun]
    congr 1
    funext y
    split_ifs <;> simp

/-- The Laplacian with zero boundary values on a finite subset of an infinite cluster is
injective (finite maximum principle). -/
theorem dirichletLaplacian_injective (hC : (Set.univ : Set C).Infinite) (S : Finset C) :
    Function.Injective (dirichletLaplacian C S) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro u hu
  let g : C → ℝ := fun y => if hy : y ∈ S then u ⟨y, hy⟩ else 0
  have hharm : ∀ x ∈ (S : Set C), componentLaplacian C g x = 0 :=
    fun x hx => congrFun hu ⟨x, hx⟩
  have hout : ∀ x, x ∉ S → g x = 0 := fun x hx => dif_neg hx
  have hle := finiteMaxPrinciple ω C hC (S : Set C) S.finite_toSet g hharm 0
    fun x hx => (hout x hx.1).le
  have hge := finiteMaxPrinciple ω C hC (S : Set C) S.finite_toSet (fun y => -g y)
    (fun x hx => by rw [componentLaplacian_neg_fun, hharm x hx, neg_zero]) 0
    fun x hx => by rw [hout x hx.1, neg_zero]
  funext z
  have h1 := hle z.val z.prop
  have h2 := hge z.val z.prop
  have h3 : g z.val = u z := dif_pos z.prop
  simp only [Pi.zero_apply]
  linarith

/-- The Dirichlet problem on a finite subset `S` of an infinite cluster: there is `h` harmonic on
`S` with `h = g` off `S`. -/
theorem exists_harmonic_extension (hC : (Set.univ : Set C).Infinite) (S : Finset C)
    (g : C → ℝ) :
    ∃ h : C → ℝ, (∀ z, z ∉ S → h z = g z) ∧ ∀ z ∈ S, componentLaplacian C h z = 0 := by
  obtain ⟨u, hu⟩ := (LinearMap.injective_iff_surjective.1 (dirichletLaplacian_injective C hC S))
    fun z : S => -componentLaplacian C g z.val
  refine ⟨fun y => g y + (if hy : y ∈ S then u ⟨y, hy⟩ else 0),
    fun z hz => by simp only [dif_neg hz, add_zero], fun z hz => ?_⟩
  rw [componentLaplacian_add_fun]
  have h1 := congrFun hu ⟨z, hz⟩
  change componentLaplacian C (fun y => if hy : y ∈ S then u ⟨y, hy⟩ else 0) z =
    -componentLaplacian C g z at h1
  linarith

open Classical in
/-- `Σ_S φ Δψ` written as a symmetric expression, for `ψ` vanishing off `S`. -/
theorem sum_mul_componentLaplacian_eq (S : Finset C) (φ ψ : C → ℝ)
    (hψ : ∀ z, z ∉ S → ψ z = 0) :
    ∑ z ∈ S, φ z * componentLaplacian C ψ z =
      ∑ z ∈ S, ∑ w ∈ S, (if (componentGraph C).Adj z w then φ z * ψ w else 0) -
        ∑ z ∈ S, ((componentGraph C).degree z : ℝ) * (φ z * ψ z) := by
  classical
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun z _ => ?_
  have h1 : ∑ w ∈ (componentGraph C).neighborFinset z, ψ w =
      ∑ w ∈ S, if (componentGraph C).Adj z w then ψ w else 0 := by
    rw [← Finset.sum_filter, ← Finset.sum_filter_of_ne (p := fun w => w ∈ S)
      fun w _ hw => by_contra fun h => hw (hψ w h)]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext w
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
    exact and_comm
  have h2 : componentLaplacian C ψ z =
      ∑ w ∈ (componentGraph C).neighborFinset z, ψ w - ((componentGraph C).degree z : ℝ) * ψ z := by
    rw [componentLaplacian, Finset.sum_sub_distrib, Finset.sum_const,
      SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul]
  rw [h2, h1, mul_sub, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun w _ => by rw [mul_ite, mul_zero]
  · ring

open Classical in
/-- Green's second identity on a finite set: `Σ_S φ Δψ = Σ_S ψ Δφ` for `φ, ψ` vanishing off
`S`. -/
theorem sum_mul_componentLaplacian_comm (S : Finset C) (φ ψ : C → ℝ)
    (hφ : ∀ z, z ∉ S → φ z = 0) (hψ : ∀ z, z ∉ S → ψ z = 0) :
    ∑ z ∈ S, φ z * componentLaplacian C ψ z = ∑ z ∈ S, ψ z * componentLaplacian C φ z := by
  rw [sum_mul_componentLaplacian_eq C S φ ψ hψ, sum_mul_componentLaplacian_eq C S ψ φ hφ]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun w _ => ?_
    rw [(componentGraph C).adj_comm, mul_comm]
  · exact Finset.sum_congr rfl fun z _ => by ring

end Dirichlet


/-- On the outer boundary of `𝒞_∞ ∩ B_n`, `n ≤ |w| < n + 1`. -/
theorem outerBoundary_ball_bounds (C : OpenComponent ω) {n : ℝ} {w : C}
    (hw : w ∈ outerBoundary C (componentEuclideanBall C 0 n : Set C)) :
    n ≤ eucl w.val ∧ eucl w.val < n + 1 := by
  obtain ⟨hw, z, hz, hwz⟩ := hw
  rw [Finset.mem_coe, mem_componentEuclideanBall, dist_latticeEuclideanEmbedding_zero] at hw hz
  refine ⟨not_lt.1 hw, ?_⟩
  have hwz' : (openGraph ω).Adj w.val z.val := hwz
  have h1 := norm_embedding_sub_le_one_of_adj (openGraph_le ω hwz')
  have h2 := norm_sub_norm_le (latticeEuclideanEmbedding w.val) (latticeEuclideanEmbedding z.val)
  change ‖latticeEuclideanEmbedding w.val‖ < n + 1
  change ‖latticeEuclideanEmbedding z.val‖ < n at hz
  linarith

/-- For `n ≤ r < n + 1` and `1 / n < ε c`: `-log n / c - ε < -log r / c ≤ -log n / c`. -/
theorem neg_log_div_bounds {n r ε c : ℝ} (hn : 0 < n) (hnr : n ≤ r) (hr : r < n + 1)
    (hc : 0 < c) (hε : 0 < ε) (hnε : 1 / (ε * c) < n) :
    -Real.log n / c - ε < -Real.log r / c ∧ -Real.log r / c ≤ -Real.log n / c := by
  have hr0 : 0 < r := by linarith
  have h1 : Real.log n ≤ Real.log r := Real.log_le_log hn hnr
  have h2 : Real.log r - Real.log n < 1 / n := by
    rw [← Real.log_div hr0.ne' hn.ne']
    have h3 := Real.log_le_sub_one_of_pos (div_pos hr0 hn)
    have h4 : r / n - 1 < 1 / n := by
      rw [div_sub_one hn.ne', div_lt_div_iff_of_pos_right hn]
      linarith
    linarith
  have h5 : 1 / n < ε * c := by
    rw [div_lt_iff₀ hn]
    linarith [(div_lt_iff₀ (mul_pos hε hc)).1 hnε, mul_comm n (ε * c)]
  constructor
  · have h6 : (-Real.log n / c - ε) * c < (-Real.log r / c) * c := by
      rw [sub_mul, div_mul_cancel₀ _ hc.ne', div_mul_cancel₀ _ hc.ne']
      nlinarith
    exact lt_of_mul_lt_mul_right h6 hc.le
  · exact (div_le_div_iff_of_pos_right hc).2 (neg_le_neg h1)

/-- Symmetry of the normalized Green function (deterministic): if every column satisfies
`G(·, y) - Ḡ → K(y)` at infinity, then `G(x, y) - K(y) = G(y, x) - K(x)`. -/
theorem greenFamily_symm (C : OpenComponent ω) (hC : (Set.univ : Set C).Infinite)
    {G : C → C → ℝ} (hG : IsGreenFamily C G) (κ : {a : ℝ // 0 < a}) (K : C → ℝ)
    (hK : ∀ y, Tendsto (fun x => G x y - greenLog κ x.val) cofinite (𝓝 (K y))) (x y : C) :
    G x y - K y = G y x - K x := by
  classical
  refine eq_of_forall_dist_le fun η hη => ?_
  rw [Real.dist_eq]
  set ε := η / 4 with hε_def
  have hε : 0 < ε := by positivity
  set c := 2 * Real.pi * κ.val with hc_def
  have hc : 0 < c := by have := κ.prop; positivity
  have hfin : ∀ v : C, {w : C | ¬ dist (G w v - greenLog κ w.val) (K v) < ε}.Finite :=
    fun v => Filter.eventually_cofinite.1 (Metric.tendsto_nhds.1 (hK v) ε hε)
  obtain ⟨R₀, hR₀⟩ := (((hfin x).union (hfin y)).image fun w : C => eucl w.val).bddAbove
  set M := max (max R₀ (max (eucl x.val) (eucl y.val))) (1 / (ε * c)) with hM_def
  have hM1 : R₀ ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
  have hMx : eucl x.val ≤ M :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)
  have hMy : eucl y.val ≤ M :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)
  have hM2 : 1 / (ε * c) ≤ M := le_max_right _ _
  set n := M + 1 with hn_def
  have hn0 : 0 < n := by
    have : 0 < 1 / (ε * c) := by positivity
    linarith
  set S := componentEuclideanBall C 0 n with hS_def
  have hmem : ∀ v : C, eucl v.val < n → v ∈ S := fun v hv => by
    rw [hS_def, mem_componentEuclideanBall, dist_latticeEuclideanEmbedding_zero]
    exact hv
  have hxS : x ∈ S := hmem x (by linarith)
  have hyS : y ∈ S := hmem y (by linarith)
  set L := -Real.log n / c with hL_def
  -- the values of the columns `x`, `y` on the outer boundary of `S`
  have hbd : ∀ v : C, (v = x ∨ v = y) → ∀ w ∈ outerBoundary C (S : Set C),
      L + K v - 2 * ε ≤ G w v ∧ G w v ≤ L + K v + ε := by
    intro v hv w hw
    obtain ⟨hw1, hw2⟩ := outerBoundary_ball_bounds C hw
    have hgood : dist (G w v - greenLog κ w.val) (K v) < ε := by
      by_contra hbad
      have hwF : w ∈ {w : C | ¬ dist (G w x - greenLog κ w.val) (K x) < ε} ∪
          {w : C | ¬ dist (G w y - greenLog κ w.val) (K y) < ε} := by
        rcases hv with rfl | rfl
        · exact Or.inl hbad
        · exact Or.inr hbad
      have := hR₀ (Set.mem_image_of_mem (fun w : C => eucl w.val) hwF)
      linarith
    rw [Real.dist_eq, abs_lt] at hgood
    have hlog := neg_log_div_bounds hn0 hw1 hw2 hc hε (by linarith)
    have hgl : greenLog κ w.val = -Real.log (eucl w.val) / c := rfl
    constructor <;> linarith [hlog.1, hlog.2]
  -- harmonic extensions of the columns off `S`
  obtain ⟨hx_, hxo, hxh⟩ := exists_harmonic_extension C hC S fun w => G w x
  obtain ⟨hy_, hyo, hyh⟩ := exists_harmonic_extension C hC S fun w => G w y
  have hmax : ∀ (v : C) (hv : v = x ∨ v = y) (h_ : C → ℝ), (∀ z, z ∉ S → h_ z = G z v) →
      (∀ z ∈ S, componentLaplacian C h_ z = 0) → ∀ z ∈ S,
        L + K v - 2 * ε ≤ h_ z ∧ h_ z ≤ L + K v + ε := by
    intro v hv h_ ho hh z hz
    have hup := finiteMaxPrinciple ω C hC (S : Set C) S.finite_toSet h_ hh (L + K v + ε)
      (fun w hw => by rw [ho w hw.1]; exact (hbd v hv w hw).2) z hz
    have hlo := finiteMaxPrinciple ω C hC (S : Set C) S.finite_toSet (fun w => -h_ w)
      (fun w hw => by rw [componentLaplacian_neg_fun, hh w hw, neg_zero])
      (-(L + K v - 2 * ε)) (fun w hw => by rw [ho w hw.1]; linarith [(hbd v hv w hw).1]) z hz
    exact ⟨by linarith, hup⟩
  have hyx := hmax y (Or.inr rfl) hy_ hyo hyh x hxS
  have hxy := hmax x (Or.inl rfl) hx_ hxo hxh y hyS
  -- the Dirichlet Green function `G_S = G - h` is symmetric
  have hlap : ∀ (v : C) (h_ : C → ℝ), (∀ z ∈ S, componentLaplacian C h_ z = 0) → ∀ z ∈ S,
      componentLaplacian C (fun w => G w v - h_ w) z = -(if z = v then 1 else 0) := by
    intro v h_ hh z hz
    rw [componentLaplacian_sub_fun, hh z hz, sub_zero]
    have := (hG v).1 z
    linarith
  have hsum : ∀ (v v' : C) (h_ h' : C → ℝ), v' ∈ S → (∀ z ∈ S, componentLaplacian C h' z = 0) →
      ∑ z ∈ S, (G z v - h_ z) * componentLaplacian C (fun w => G w v' - h' w) z =
        -(G v' v - h_ v') := by
    intro v v' h_ h' hv' hh
    rw [Finset.sum_congr rfl fun z hz => by rw [hlap v' h' hh z hz]]
    simp only [mul_neg, mul_ite, mul_one, mul_zero, Finset.sum_neg_distrib, Finset.sum_ite_eq',
      if_pos hv']
  have hsym := sum_mul_componentLaplacian_comm C S (fun w => G w x - hx_ w)
    (fun w => G w y - hy_ w) (fun z hz => by simp only [hxo z hz, sub_self])
    (fun z hz => by simp only [hyo z hz, sub_self])
  rw [hsum x y hx_ hy_ hyS hyh, hsum y x hy_ hx_ hxS hxh] at hsym
  rw [abs_le]
  constructor <;> linarith [hyx.1, hyx.2, hxy.1, hxy.2]

/-- `GreenSymmetry p` from the asymptotics of the Green columns (`PotentialAsymptotic p` applied
to `f = δ_y`, `y ∈ ℤ²`): `κ(y) = lim (G(·, y) - Ḡ)`. -/
theorem greenSymmetry_of_potentialAsymptotic {p : unitInterval} (hpa : PotentialAsymptotic p) :
    GreenSymmetry p := by
  obtain ⟨κ, hκ⟩ := hpa
  have hfs : ∀ y : Vertex 2, (Function.support (Pi.single y 1 : Vertex 2 → ℤ)).Finite :=
    fun y => (Set.finite_singleton y).subset Pi.support_single_subset
  have hall : ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ y : Vertex 2, ∀ h : HasUniqueInfiniteOpenComponent ω,
      ∃ L : ℝ, ∀ G, IsGreenFamily (uniqueInfiniteComponent h) G →
        Tendsto (fun x => potential (uniqueInfiniteComponent h) G (Pi.single y 1) x -
          (mass (uniqueInfiniteComponent h) (Pi.single y 1) : ℝ) * greenLog κ x.val) cofinite
          (𝓝 L) :=
    ae_all_iff.2 fun y => hκ _ (hfs y)
  filter_upwards [hall] with ω hω h G hG
  have hC : (Set.univ : Set (uniqueInfiniteComponent h)).Infinite :=
    Set.infinite_univ_iff.2 (Set.infinite_coe_iff.2 (uniqueInfiniteComponent_infinite h))
  choose L hL using fun y : uniqueInfiniteComponent h => hω y.val h
  refine ⟨L, fun x y => greenFamily_symm _ hC hG κ L (fun v => ?_) x y⟩
  have hne : ∀ z : uniqueInfiniteComponent h, z ≠ v →
      (Pi.single v.val 1 : Vertex 2 → ℤ) z.val = 0 :=
    fun z hz => Pi.single_eq_of_ne (fun h => hz (Subtype.ext h)) _
  have hpot : ∀ x, potential (uniqueInfiniteComponent h) G (Pi.single v.val 1) x = G x v := by
    intro x
    rw [potential, finsum_eq_single _ v fun z hz => by rw [hne z hz, Int.cast_zero, zero_mul],
      Pi.single_eq_same, Int.cast_one, one_mul]
  have hmass : mass (uniqueInfiniteComponent h) (Pi.single v.val 1) = 1 := by
    rw [mass, finsum_eq_single _ v hne, Pi.single_eq_same]
  have h1 := hL v G hG
  simp only [hpot, hmass, Int.cast_one, one_mul] at h1
  exact h1

/-- `GreenSymmetry p` for `p_c < p < 1`, from the quantitative Green asymptotics
(`SupercriticalBondGreenQuantitative`). -/
theorem greenSymmetry (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    {p : unitInterval} (hp : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    GreenSymmetry p :=
  greenSymmetry_of_potentialAsymptotic (potentialAsymptotic hGQ hp hp1)

end Rigidity.Proofs.Section5
