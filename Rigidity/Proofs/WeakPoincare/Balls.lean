import PercolationClusterHomogenization.Proofs.Cluster.GehringCubes
import PercolationClusterHomogenization.Proofs.Density.ScaleInputsFaithful

/-!
# Good balls of the supercritical infinite cluster in every dimension

The discrete objects and the statements of the volume regularity and of the weak Poincaré
inequality on Euclidean balls of the infinite cluster `𝒞_∞` of supercritical bond percolation on
`ℤ^d`, `d ≥ 2`, in the forms used by Barlow (*Random walks on supercritical percolation clusters*,
Ann. Probab. 32 (2004), Definition 1.7, Theorem 2.18 and Lemma 2.19) and by Dario–Gu
(*Quantitative homogenization of the parabolic and elliptic Green's functions on percolation
clusters*, Proposition 2.7 in its weak form).

* `latticeDist x y` is the Euclidean distance; `clusterBall K y r` is `K ∩ B_r(y)`, the vertices of
  the component `K` at distance less than `r` from `y`; `finAvg U u` is the average `(u)_U`.
* `nbrEnergy ω U u = Σ_{x ∈ U} Σ_{z ∈ U, z ∼ x} (u(z) - u(x))²`, the Dirichlet energy of `u` over
  the open edges with both endpoints in `U` (each edge counted twice).
* `IsGoodBall ω K CV CP L z r`: Barlow's Definition 1.7 for the Euclidean ball `K ∩ B_r(z)` with
  the counting measure: the volume bound (1.15) `CV r^d ≤ |K ∩ B_r(z)|` and the weak Poincaré
  inequality (1.16) `Σ_{K ∩ B_r(z)} (u - (u)_{K ∩ B_r(z)})² ≤ CP r² Σ_{edges of K ∩ B_{Lr}(z)} |∇u|²`.

Named statements:

* `ClusterGoodBalls d`: Barlow's Theorem 2.18 (a), (b) with the random scale of Lemma 2.19 at a
  fixed centre: above a minimal scale `M(y) ≤ O_s(C)`, the ball `𝒞_∞ ∩ B_R(y)` is good and
  `|𝒞_∞ ∩ B_R(y)| ≤ C R^d`.
* `ClusterVeryGoodBalls d`: Barlow's Theorem 2.18 (c) with Lemma 2.19: for `θ > 0` and `A ≥ 1`,
  above a random scale `S(y) ≤ O_s(C')`, every ball `𝒞_∞ ∩ B_r(z)` with `|z - y| ≤ A R` and
  `r ≥ R^θ` is good, with constants `CV, CP, L` not depending on `θ` and `A` (`θ = 1/(d+2)`,
  `A = 1` is Barlow's very good ball `B(y, R)` with `N_B ≤ R^{1/(d+2)}`).
* `ClusterPoincare d`: Dario–Gu, Proposition 2.7, weak form, in the normalized `L̲²` averages:
  `‖u - (u)_{𝒞_∞ ∩ B_R(y)}‖_{L̲²} ≤ C R ‖∇u‖_{L̲²(𝒞_∞ ∩ B_{LR}(y))}` for `R ≥ M(y) ≤ O_s(C)`.

All three statements hold for `d ≥ 2`: `clusterGoodBalls_holds` (`GoodBallsHolds.lean`),
`clusterVeryGoodBalls_holds` and `clusterPoincare_holds` (`VeryGood.lean`).

Barlow works with the balls of the graph distance of `𝒞_∞` and the measure `μ_x = deg(x)`; here the
balls are Euclidean and the measure is the counting measure, as in Dario–Gu. The Euclidean balls are
a different family from the balls of the graph distance, not a change of constants; the counting
measure changes the constants only (`1 ≤ μ_x ≤ 2d` on `𝒞_∞`). The printed form of Proposition 2.7
of Dario–Gu, with the gradient on the same ball, fails in every dimension for the reason given at
`Rigidity.Green.ClusterPoincareTwo`.
-/

open Finset LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Cluster

namespace Rigidity.WeakPoincare

variable {d : ℕ}

/-! ### The Euclidean distance -/

/-- The Euclidean distance between two lattice points. -/
noncomputable def latticeDist (x y : Vertex d) : ℝ :=
  ‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding y‖

theorem latticeDist_nonneg (x y : Vertex d) : 0 ≤ latticeDist x y := norm_nonneg _

theorem latticeDist_comm (x y : Vertex d) : latticeDist x y = latticeDist y x := by
  unfold latticeDist
  rw [norm_sub_rev]

theorem latticeDist_self (x : Vertex d) : latticeDist x x = 0 := by
  simp [latticeDist]

theorem latticeDist_triangle (x y z : Vertex d) :
    latticeDist x z ≤ latticeDist x y + latticeDist y z := by
  unfold latticeDist
  calc ‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding z‖
      = ‖(latticeEuclideanEmbedding x - latticeEuclideanEmbedding y) +
          (latticeEuclideanEmbedding y - latticeEuclideanEmbedding z)‖ := by
        congr 1
        abel
    _ ≤ _ := norm_add_le _ _

theorem latticeDist_sq (x y : Vertex d) :
    latticeDist x y ^ 2 = ∑ i, ((x i : ℝ) - y i) ^ 2 := by
  rw [latticeDist, EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp only [PiLp.sub_apply, Real.norm_eq_abs, sq_abs]
  rfl

/-- A coordinate difference is at most the Euclidean distance. -/
theorem abs_sub_le_latticeDist (x y : Vertex d) (i : Fin d) :
    |(x i : ℝ) - y i| ≤ latticeDist x y := by
  have h : ((x i : ℝ) - y i) ^ 2 ≤ latticeDist x y ^ 2 := by
    rw [latticeDist_sq]
    exact Finset.single_le_sum (f := fun j => ((x j : ℝ) - y j) ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ i)
  have := sq_le_sq.1 h
  rwa [abs_of_nonneg (latticeDist_nonneg x y)] at this

/-- The Euclidean distance is at most the `ℓ¹` distance. -/
theorem latticeDist_le_sum_abs (x y : Vertex d) :
    latticeDist x y ≤ ∑ i, |(x i : ℝ) - y i| := by
  have h0 : 0 ≤ ∑ i, |(x i : ℝ) - y i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h : latticeDist x y ^ 2 ≤ (∑ i, |(x i : ℝ) - y i|) ^ 2 := by
    rw [latticeDist_sq]
    calc ∑ i, ((x i : ℝ) - y i) ^ 2 = ∑ i, |(x i : ℝ) - y i| ^ 2 :=
          Finset.sum_congr rfl fun i _ => (sq_abs _).symm
      _ ≤ _ := Finset.sum_sq_le_sq_sum_of_nonneg fun _ _ => abs_nonneg _
  have := sq_le_sq.1 h
  rwa [abs_of_nonneg (latticeDist_nonneg x y), abs_of_nonneg h0] at this

/-- If every coordinate difference is less than `a`, the Euclidean distance is less than `d a`. -/
theorem latticeDist_lt_of_abs_lt (hd : 0 < d) {x y : Vertex d} {a : ℝ}
    (h : ∀ i, |(x i : ℝ) - y i| < a) : latticeDist x y < d * a := by
  have hne : (Finset.univ : Finset (Fin d)).Nonempty := ⟨⟨0, hd⟩, Finset.mem_univ _⟩
  calc latticeDist x y ≤ ∑ i, |(x i : ℝ) - y i| := latticeDist_le_sum_abs x y
    _ < ∑ _i : Fin d, a := Finset.sum_lt_sum_of_nonempty hne fun i _ => h i
    _ = d * a := by simp

/-! ### Balls of a component -/

/-- `K ∩ B_r(y)`: the vertices of `K` at Euclidean distance less than `r` from `y`. -/
noncomputable def clusterBall {ω : Configuration d} (K : OpenComponent ω) (y : Vertex d) (r : ℝ) :
    Finset (Vertex d) := by
  classical
  exact (box y (⌈r⌉₊ : ℤ)).filter (fun x => x ∈ K.supp ∧ latticeDist x y < r)

theorem mem_clusterBall {ω : Configuration d} {K : OpenComponent ω} {y x : Vertex d} {r : ℝ} :
    x ∈ clusterBall K y r ↔ x ∈ K.supp ∧ latticeDist x y < r := by
  classical
  unfold clusterBall
  rw [Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨mem_box.2 fun i => ?_, h⟩
    have h1 := (abs_sub_le_latticeDist x y i).trans_lt h.2
    have h2 : r ≤ (⌈r⌉₊ : ℝ) := Nat.le_ceil r
    have h3 : |((x i - y i : ℤ) : ℝ)| < ((⌈r⌉₊ : ℤ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h3.le

theorem clusterBall_mono {ω : Configuration d} {K : OpenComponent ω} {y : Vertex d} {r r' : ℝ}
    (h : r ≤ r') : clusterBall K y r ⊆ clusterBall K y r' := by
  intro x hx
  rw [mem_clusterBall] at hx ⊢
  exact ⟨hx.1, hx.2.trans_le h⟩

/-- `|K ∩ B_r(y)| ≤ (5 r)^d` for `r ≥ 1`. -/
theorem card_clusterBall_le {ω : Configuration d} (K : OpenComponent ω) (y : Vertex d) {r : ℝ}
    (hr : 1 ≤ r) : ((clusterBall K y r).card : ℝ) ≤ (5 * r) ^ d := by
  classical
  have h1 : (clusterBall K y r).card ≤ (box y (⌈r⌉₊ : ℤ)).card := by
    unfold clusterBall
    convert Finset.card_filter_le _ _
  have h2 : ((clusterBall K y r).card : ℝ) ≤ (box y (⌈r⌉₊ : ℤ)).card := by exact_mod_cast h1
  rw [card_box y (by positivity)] at h2
  refine h2.trans (pow_le_pow_left₀ (by positivity) ?_ d)
  have h3 : (⌈r⌉₊ : ℝ) < r + 1 := Nat.ceil_lt_add_one (by linarith)
  push_cast
  linarith

/-! ### Averages and energies -/

/-- The average `(u)_U = |U|^{-1} Σ_{x ∈ U} u(x)`. -/
noncomputable def finAvg (U : Finset (Vertex d)) (u : Vertex d → ℝ) : ℝ :=
  (∑ x ∈ U, u x) / U.card

/-- `Σ_{x ∈ U} Σ_{z ∈ U, z ∼ x} (u(z) - u(x))²`, over the open edges with both endpoints in `U`. -/
noncomputable def nbrEnergy (ω : Configuration d) (U : Finset (Vertex d)) (u : Vertex d → ℝ) :
    ℝ := by
  classical
  exact ∑ x ∈ U, ∑ z ∈ U.filter (fun z => (openGraph ω).Adj x z), (u z - u x) ^ 2

theorem nbrEnergy_nonneg (ω : Configuration d) (U : Finset (Vertex d)) (u : Vertex d → ℝ) :
    0 ≤ nbrEnergy ω U u := by
  unfold nbrEnergy
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem nbrEnergy_mono (ω : Configuration d) {U V : Finset (Vertex d)} (h : U ⊆ V)
    (u : Vertex d → ℝ) : nbrEnergy ω U u ≤ nbrEnergy ω V u := by
  classical
  unfold nbrEnergy
  refine (Finset.sum_le_sum fun x _ => Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset_filter _ h) fun _ _ _ => sq_nonneg _).trans ?_
  exact Finset.sum_le_sum_of_subset_of_nonneg h fun _ _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The average minimizes the sum of squares: `Σ_U (u - (u)_U)² ≤ Σ_U (u - a)²`. -/
theorem sum_sq_sub_finAvg_le (U : Finset (Vertex d)) (u : Vertex d → ℝ) (a : ℝ) :
    ∑ x ∈ U, (u x - finAvg U u) ^ 2 ≤ ∑ x ∈ U, (u x - a) ^ 2 := by
  rcases U.eq_empty_or_nonempty with rfl | hne
  · simp
  have hc : (0 : ℝ) < U.card := by exact_mod_cast hne.card_pos
  have hsum : ∑ x ∈ U, (u x - finAvg U u) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, finAvg]
    field_simp
    ring
  have e : ∑ x ∈ U, (u x - a) ^ 2 = ∑ x ∈ U, (u x - finAvg U u) ^ 2 +
      2 * (finAvg U u - a) * ∑ x ∈ U, (u x - finAvg U u) + U.card * (finAvg U u - a) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    have : ∑ x ∈ U, (u x - a) ^ 2 = ∑ x ∈ U, ((u x - finAvg U u) ^ 2 +
        2 * (finAvg U u - a) * (u x - finAvg U u) + (finAvg U u - a) ^ 2) :=
      Finset.sum_congr rfl fun x _ => by ring
    rw [this, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  rw [e, hsum, mul_zero, add_zero]
  have : 0 ≤ (U.card : ℝ) * (finAvg U u - a) ^ 2 := by positivity
  linarith

/-! ### Good balls and the named statements -/

/-- **Barlow 2004, Definition 1.7** (good ball), for the Euclidean ball `K ∩ B_r(z)` of a component
`K` with the counting measure: the volume bound (1.15) `CV r^d ≤ |K ∩ B_r(z)|` and the weak
Poincaré inequality (1.16) with the gradient on the open edges inside `K ∩ B_{Lr}(z)`. -/
def IsGoodBall (ω : Configuration d) (K : OpenComponent ω) (CV CP L : ℝ) (z : Vertex d)
    (r : ℝ) : Prop :=
  CV * r ^ d ≤ (clusterBall K z r).card ∧
    ∀ u : Vertex d → ℝ, ∑ x ∈ clusterBall K z r, (u x - finAvg (clusterBall K z r) u) ^ 2 ≤
      CP * r ^ 2 * nbrEnergy ω (clusterBall K z (L * r)) u

/-- **Barlow 2004, Theorem 2.18 (a), (b) with the random scale of Lemma 2.19**, at a fixed centre,
for Euclidean balls of `𝒞_∞` in dimension `d`.

Printed statements (Theorem 2.18 (a), (b)): on the event `H(Q, α) ∩ D(Q, α)` for a cube `Q` of side
`n`, for `C_H n^α ≤ r ≤ n` and `y ∈ C^∨(Q⁺)` well inside `Q`,
`C_V r^d ≤ |B_ω(y, r)| ≤ C_0 r^d` (2.23) and
`∫_{B_ω(y,r)} (f - f̄)² dμ ≤ C_P r² ∫_{E(B_ω(y, C_W r))} |∇f|² dν` (2.24); (Lemma 2.19) for each `x`
there is `M_x` with `P(M_x ≥ n) ≤ c exp(-c' n^{αβ})` such that the event holds for every cube of
side `n ≥ M_x` containing `x`. Here: for every `R ≥ M(y)`, `M(y) ≤ O_s(C)`, the ball
`𝒞_∞ ∩ B_R(y)` is good with `CV = C⁻¹`, `CP = C` and dilation `L` and `|𝒞_∞ ∩ B_R(y)| ≤ C R^d`.
The balls are Euclidean and `y` is any lattice point. -/
def ClusterGoodBalls (d : ℕ) [NeZero d] : Prop :=
  ∀ p : unitInterval, criticalProbability d < (p : ℝ) → (p : ℝ) < 1 →
    ∃ s C L : ℝ, 0 < s ∧ 0 < C ∧ 1 ≤ L ∧ ∀ y : Vertex d,
      ∃ M : Configuration d → ℝ, Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧ IsOsBond d p M s C ∧
        ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω, ∀ R : ℝ, M ω ≤ R →
          IsGoodBall ω (uniqueInfiniteComponent h) C⁻¹ C L y R ∧
            ((clusterBall (uniqueInfiniteComponent h) y R).card : ℝ) ≤ C * R ^ d

/-- **Barlow 2004, Theorem 2.18 (c) with Lemma 2.19** (very good balls), for Euclidean balls of
`𝒞_∞` in dimension `d`.

Printed statement (Theorem 2.18 (c), Definition 1.7): if `(C_H n^α)^{d+2} ≤ R ≤ n`, then
`B_ω(y, R)` is very good with `N_{B_ω(y,R)} ≤ C_H n^α`: every ball `B(y', r) ⊆ B(y, R)` with
`N_B ≤ r ≤ R` is good. Here: there are constants `C, L` such that for every `θ > 0` and `A ≥ 1`
there is a random scale `S(y) ≤ O_s(C')` above which every ball `𝒞_∞ ∩ B_r(z)` with
`|z - y| ≤ A R` and `r ≥ R^θ` is good (with `CV = C⁻¹`, `CP = C`, dilation `L`) and has at most
`C r^d` points. -/
def ClusterVeryGoodBalls (d : ℕ) [NeZero d] : Prop :=
  ∀ p : unitInterval, criticalProbability d < (p : ℝ) → (p : ℝ) < 1 →
    ∃ C L : ℝ, 0 < C ∧ 1 ≤ L ∧ ∀ θ A : ℝ, 0 < θ → 1 ≤ A →
      ∃ s C' : ℝ, 0 < s ∧ 0 < C' ∧ ∀ y : Vertex d,
        ∃ S : Configuration d → ℝ, Measurable S ∧ (∀ ω, 0 ≤ S ω) ∧ IsOsBond d p S s C' ∧
          ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω, ∀ R : ℝ, S ω ≤ R →
            ∀ z : Vertex d, latticeDist z y ≤ A * R → ∀ r : ℝ, R ^ θ ≤ r →
              IsGoodBall ω (uniqueInfiniteComponent h) C⁻¹ C L z r ∧
                ((clusterBall (uniqueInfiniteComponent h) z r).card : ℝ) ≤ C * r ^ d

/-- **Dario–Gu, Proposition 2.7** (Poincaré inequality on `𝒞_∞`), `p = 2`, in dimension `d`, in
the weak form with the gradient on the dilated ball `𝒞_∞ ∩ B_{LR}(y)`.

Printed statement (lines 979-993 of the source): *There exist a constant `C < ∞` and an exponent
`s > 0` such that, for any `y ∈ ℤ^d`, there exists a non-negative random variable
`M_Poinc(y) ≤ O_s(C)` such that for each radius `R ≥ M_Poinc(y)` and each function
`u : 𝒞_∞ ∩ B_R(y) → ℝ`, `‖u - (u)_{𝒞_∞ ∩ B_R(y)}‖_{L̲²(𝒞_∞ ∩ B_R(y))} ≤ C R ‖∇u‖_{L̲²(𝒞_∞ ∩ B_R(y))}`.*
The printed form fails (see `Rigidity.Green.ClusterPoincareTwo`); the gradient is taken here over
the open edges inside `𝒞_∞ ∩ B_{LR}(y)`, `|∇u|²(x) = Σ_{z ∼ x} (u(z) - u(x))²`. -/
def ClusterPoincare (d : ℕ) [NeZero d] : Prop :=
  ∀ p : unitInterval, criticalProbability d < (p : ℝ) → (p : ℝ) < 1 →
    ∃ s C L : ℝ, 0 < s ∧ 0 < C ∧ 1 ≤ L ∧ ∀ y : Vertex d,
      ∃ M : Configuration d → ℝ, Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧ IsOsBond d p M s C ∧
        ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω, ∀ R : ℝ, M ω ≤ R →
          ∀ u : Vertex d → ℝ,
            Real.sqrt ((∑ x ∈ clusterBall (uniqueInfiniteComponent h) y R,
                (u x - finAvg (clusterBall (uniqueInfiniteComponent h) y R) u) ^ 2) /
                (clusterBall (uniqueInfiniteComponent h) y R).card) ≤
              C * R * Real.sqrt (nbrEnergy ω (clusterBall (uniqueInfiniteComponent h) y (L * R)) u /
                (clusterBall (uniqueInfiniteComponent h) y (L * R)).card)

end Rigidity.WeakPoincare
