import Rigidity.Proofs.Green.Cheeger
import Rigidity.Proofs.Green.ClusterFaberKrahn
import Rigidity.External.WellConnected
import Rigidity.External.PlanarInputs

/-!
# Green columns of the infinite cluster from isoperimetry in large cubes

`ClusterIsoperimetry d p ε` says that, for each fixed pole `y`, almost surely there are `κ > 0`
and `R₀` such that for every `R ≥ R₀`, every finite set `A` of vertices of the infinite cluster
inside the cube `y + Q_R` with at least `R^ε` vertices has at least `κ |A|^{(d-1)/d}` boundary
edges in the cluster. This is the isoperimetric inequality of Benjamini-Mossel and
Mathieu-Remy for the supercritical cluster, required only for sets of polynomial size `R^ε`
(they prove it above a power of `log R`).

A graph ball of radius `R` in the cluster lies in the cube `y + Q_R`, so the discrete Cheeger
inequality (`Cheeger.lean`) gives the Faber-Krahn inequality on the balls with constant
`a₀ R^{-2ε}`, and for `d ≥ 3` and `(d/2)(1 - 2ε) > 1` (for instance `ε ≤ 1/12`) the cluster Green
columns exist and are unique (`ClusterFaberKrahn.lean`). Together with the planar statement this
gives the Green-column input `LatticeProb.External.SupercriticalBondGreenColumnExistence`
(`supercriticalBondGreenColumnExistence_of_isoperimetry`).
-/

open MeasureTheory LatticeProb.Percolation LatticeProb.Graph
open scoped Classical

namespace Rigidity.Green

variable {d : ℕ}

/-- Almost surely, for all large `R`, the isoperimetric inequality of dimension `d` holds for the
sets of at least `R^ε` vertices of the infinite cluster inside the cube `y + Q_R`. -/
def ClusterIsoperimetry (d : ℕ) [NeZero d] (p : unitInterval) (ε : ℝ) : Prop :=
  ∀ y : Vertex d, ∀ᵐ ω ∂latticeBondLaw d p,
    ∀ h : HasUniqueInfiniteOpenComponent ω, ∀ _hy : y ∈ (uniqueInfiniteComponent h).supp,
      ∃ κ : ℝ, 0 < κ ∧ ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
        IsoperimetricOn (componentGraph (uniqueInfiniteComponent h))
          {v | v.val ∈ Rigidity.External.cubeAt y R} d κ ((R : ℝ) ^ ε)

/-- A component step changes every coordinate by at most one. -/
theorem abs_sub_le_one_of_componentGraph_adj {ω : Configuration d} {C : OpenComponent ω}
    {a b : C} (h : (componentGraph C).Adj a b) (i : Fin d) : |a.val i - b.val i| ≤ 1 := by
  have hadj : (openGraph ω).Adj a.val b.val := h
  have hsum := lattice_adj_iff_l1Dist.mp (openGraph_le ω hadj)
  have hle : |a.val i - b.val i| ≤ latticeL1Dist a.val b.val :=
    Finset.single_le_sum (fun j _ => abs_nonneg (a.val j - b.val j)) (Finset.mem_univ i)
  omega

/-- A walk of length `n` in a component stays in the cube of radius `n` around its start. -/
theorem abs_sub_le_length {ω : Configuration d} {C : OpenComponent ω} :
    ∀ {a b : C} (q : (componentGraph C).Walk a b) (i : Fin d),
      |b.val i - a.val i| ≤ q.length := by
  intro a b q i
  induction q with
  | nil => simp
  | cons hadj q ih =>
      rename_i u v w
      have h1 := abs_sub_le_one_of_componentGraph_adj hadj i
      have h2 : |w.val i - u.val i| ≤ |w.val i - v.val i| + |v.val i - u.val i| :=
        abs_sub_le _ _ _
      rw [abs_sub_comm (v.val i) (u.val i)] at h2
      simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
      linarith

/-- A graph ball of radius `R` of a component lies in the lattice cube of radius `R`. -/
theorem mem_cubeAt_of_dist_le {ω : Configuration d} (C : OpenComponent ω) {y v : C} {R : ℕ}
    (h : (componentGraph C).dist y v ≤ R) : v.val ∈ Rigidity.External.cubeAt y.val R := by
  obtain ⟨q, hq⟩ := C.connected_toSimpleGraph.exists_walk_length_eq_dist y v
  intro i
  have := abs_sub_le_length q i
  rw [hq] at this
  have hR : ((componentGraph C).dist y v : ℤ) ≤ R := by exact_mod_cast h
  exact this.trans hR

/-- Cube isoperimetry gives Faber-Krahn inequalities on the graph balls with constant
`a₀ R^{-2ε}`. -/
theorem clusterFaberKrahn_of_clusterIsoperimetry [NeZero d] {p : unitInterval} {ε : ℝ}
    (hd : 1 ≤ d) (hε : 0 ≤ ε) (hiso : ClusterIsoperimetry d p ε) :
    ClusterFaberKrahn d p d (2 * ε) := by
  intro y
  filter_upwards [hiso y] with ω hω
  intro h hy
  obtain ⟨κ, hκ, R₀, hR⟩ := hω h hy
  set C := uniqueInfiniteComponent h
  letI : Infinite C := Set.infinite_coe_iff.mpr (uniqueInfiniteComponent_infinite h)
  have hG := C.connected_toSimpleGraph
  set κ' := min κ 1 with hκ'
  have hκ'pos : 0 < κ' := lt_min hκ one_pos
  have hdpos : (0 : ℝ) < 2 * d := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  refine ⟨κ' ^ 2 / (4 * (2 * d : ℕ)), by positivity, max R₀ 1, fun R hRR => ?_⟩
  have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast le_of_max_le_right hRR
  have hRpos : (0 : ℝ) < R := by linarith
  have hs₀ : (1 : ℝ) ≤ (R : ℝ) ^ ε := Real.one_le_rpow hR1 hε
  have hisoR : IsoperimetricOn (componentGraph C) {v | (componentGraph C).dist ⟨y, hy⟩ v ≤ R}
      d κ' ((R : ℝ) ^ ε) := by
    intro U hU hs
    have hU' : (↑U : Set C) ⊆ {v | v.val ∈ Rigidity.External.cubeAt y R} :=
      fun v hv => mem_cubeAt_of_dist_le C (hU hv)
    have h1 := hR R (le_of_max_le_left hRR) U hU' hs
    have h2 : κ' * (U.card : ℝ) ^ (((d : ℝ) - 1) / d) ≤ κ * (U.card : ℝ) ^ (((d : ℝ) - 1) / d) :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    exact h2.trans h1
  have hFK := faberKrahnOn_of_isoperimetricOn hG (componentGraph_degree_le C)
    (by exact_mod_cast (by omega : 0 < d)) hκ'pos (min_le_right _ _) hs₀ hisoR
  have hconst : κ' ^ 2 / (4 * ((2 * d : ℕ) : ℝ) * ((R : ℝ) ^ ε) ^ 2) =
      κ' ^ 2 / (4 * (2 * d : ℕ)) * (R : ℝ) ^ (-(2 * ε)) := by
    have hpow : ((R : ℝ) ^ ε) ^ 2 = (R : ℝ) ^ (2 * ε) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hRpos.le]; ring_nf
    rw [hpow, Real.rpow_neg hRpos.le]
    field_simp
  rw [hconst] at hFK
  exact hFK

/-- **Green columns in dimension `d ≥ 3` from cluster isoperimetry.** -/
theorem greenColumnExistence_of_clusterIsoperimetry [NeZero d] (hd : 3 ≤ d) (hd2 : 2 ≤ d)
    (p : unitInterval) {ε : ℝ} (hε : 0 ≤ ε) (hγ : 1 < (d : ℝ) / 2 * (1 - 2 * ε))
    (hiso : ClusterIsoperimetry d p ε) (y : Vertex d) :
    ∀ᵐ ω ∂latticeBondLaw d p,
      ∀ h : HasUniqueInfiniteOpenComponent ω,
        ∀ hy : y ∈ (uniqueInfiniteComponent h).supp,
          ∃! g : uniqueInfiniteComponent h → ℝ,
            IsGreenColumn d hd2 (uniqueInfiniteComponent h) ⟨y, hy⟩ g :=
  greenColumnExistence_of_clusterFaberKrahn hd hd2 p
    (by exact_mod_cast (by omega : 0 < d)) hγ
    (clusterFaberKrahn_of_clusterIsoperimetry (by omega) hε hiso) y

/-- With `ε ≤ 1/12`, the exponent condition holds in every dimension `d ≥ 3`. -/
theorem one_lt_exponent_of_le {ε : ℝ} (hε : ε ≤ 1 / 12) (hd : 3 ≤ d) :
    1 < (d : ℝ) / 2 * (1 - 2 * ε) := by
  have : (3 : ℝ) ≤ d := by exact_mod_cast hd
  nlinarith

/-- **The Green-column input** from the planar statement and cluster isoperimetry in every
dimension `d ≥ 3` for some exponent `ε ≤ 1/12`. -/
theorem supercriticalBondGreenColumnExistence_of_isoperimetry
    (hTwo : Rigidity.External.SupercriticalBondGreenColumnExistenceTwo)
    (hiso : ∀ (d : ℕ) [NeZero d], 3 ≤ d → ∀ p : unitInterval,
      criticalProbability d < (p : ℝ) → (p : ℝ) < 1 →
        ∃ ε : ℝ, 0 ≤ ε ∧ ε ≤ 1 / 12 ∧ ClusterIsoperimetry d p ε) :
    LatticeProb.External.SupercriticalBondGreenColumnExistence := by
  intro d _ hd p hp hp1 y
  rcases Nat.lt_or_ge d 3 with hlt | h3
  · obtain rfl : d = 2 := by omega
    exact hTwo p hp hp1 y
  · obtain ⟨ε, hε0, hε, hI⟩ := hiso d h3 p hp hp1
    exact greenColumnExistence_of_clusterIsoperimetry h3 hd p hε0 (one_lt_exponent_of_le hε h3)
      hI y

end Rigidity.Green
