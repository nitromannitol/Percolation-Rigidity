import Rigidity.Proofs.S3.ChemicalDistance

/-!
# Open links inside well-connected cubes

In a well-connected cube `c + Q_N`, every cube `z + Q_M` of radius `M = ⌈N^δ/2⌉`,
`δ = 1/(10d)²`, centred in the cube is good, and its largest cluster absorbs every open path of at
least `M/100` steps inside it. A vertex which starts an open self-avoiding path of more than `M`
steps therefore lies in the largest cluster of the good cube centred at it, since the first `M`
steps of the path stay in that cube. Chaining good cubes, two such vertices of `c + Q_N` are joined
by an open path of at most `(2dN + 1)(2M + 1)^d` steps. Vertices of infinite open clusters start
such paths.
-/

namespace Rigidity.Proofs.Section5

open LatticeProb.Percolation Rigidity.External Rigidity.Proofs.S3

variable {d : ℕ}

/-- The radius `⌈N^δ/2⌉`, `δ = 1/(10d)²`, of the good subcubes of a well-connected cube of
radius `N`. -/
noncomputable def wcSubRadius (d N : ℕ) : ℕ := ⌈(N : ℝ) ^ (1 / (10 * (d : ℝ)) ^ 2) / 2⌉₊

/-- `x` starts an open self-avoiding path of more than `M` steps. -/
def StartsLongPath (ω : Configuration d) (x : Vertex d) (M : ℕ) : Prop :=
  ∃ (b : Vertex d) (p : (openGraph ω).Walk x b), p.IsPath ∧ M < p.length

/-- A vertex of an infinite open cluster starts open self-avoiding paths of every length. -/
theorem startsLongPath_of_infinite {ω : Configuration d} {x : Vertex d} (M : ℕ)
    (hx : ((openGraph ω).connectedComponentMk x).supp.Infinite) : StartsLongPath ω x M := by
  obtain ⟨y, hy, hyB⟩ : ∃ y ∈ ((openGraph ω).connectedComponentMk x).supp, y ∉ cubeAt x M :=
    (hx.sdiff (finite_cubeAt x M)).nonempty
  have hr : (openGraph ω).Reachable x y :=
    (SimpleGraph.ConnectedComponent.eq.mp
      ((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp hy)).symm
  obtain ⟨w⟩ := hr
  refine ⟨y, w.bypass, w.bypass_isPath, ?_⟩
  have hcoord := abs_getVert_sub_le (openGraph_le ω) w.bypass
  by_contra hlen
  apply hyB
  intro k
  have := hcoord w.bypass.length k
  rw [SimpleGraph.Walk.getVert_length] at this
  exact this.trans (by omega)

/-- A vertex starting an open path of more than `M` steps lies in the largest cluster of a good
cube of radius `M` centred at it. -/
theorem mem_of_isGoodCluster_of_startsLongPath {ω : Configuration d} {x : Vertex d} {M : ℕ}
    {V : Set (Vertex d)} (hV : IsGoodCluster ω x M V) (hx : StartsLongPath ω x M) : x ∈ V := by
  obtain ⟨b, p, hp, hlen⟩ := hx
  have hcoord := abs_getVert_sub_le (openGraph_le ω) p
  refine mem_of_isGoodCluster_of_isPath hV le_rfl p hp (by omega) ?_
  intro i hi k
  exact (hcoord i k).trans (by exact_mod_cast hi)

/-- **Links in well-connected cubes.** In a well-connected cube `c + Q_N`, `N ≥ 1`, two vertices
of the cube which start open paths of more than `M = ⌈N^δ/2⌉` steps are joined by an open path of
at most `(2dN + 1)(2M + 1)^d` steps. -/
theorem exists_walk_of_isWellConnected_of_startsLongPath {ω : Configuration d} {c : Vertex d}
    {N : ℕ} (hN : 1 ≤ N) (hwc : IsWellConnected ω c N) {x y : Vertex d} (hx : x ∈ cubeAt c N)
    (hy : y ∈ cubeAt c N) (hxl : StartsLongPath ω x (wcSubRadius d N))
    (hyl : StartsLongPath ω y (wcSubRadius d N)) :
    ∃ p : (openGraph ω).Walk x y,
      p.length ≤ (2 * d * N + 1) * (2 * wcSubRadius d N + 1) ^ d := by
  obtain ⟨-, -, hgood⟩ := hwc
  have hN1 : (1 : ℝ) ≤ (N : ℝ) ^ (1 / (10 * (d : ℝ)) ^ 2) :=
    Real.one_le_rpow (by exact_mod_cast hN) (by positivity)
  have hM : 1 ≤ wcSubRadius d N :=
    Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (by positivity)).ne'
  have hMN : (wcSubRadius d N : ℝ) ≤ N / 10 := by
    have := Nat.ceil_lt_add_one (show 0 ≤ (N : ℝ) ^ (1 / (10 * (d : ℝ)) ^ 2) / 2 by positivity)
    unfold wcSubRadius
    linarith
  have hV : ∀ z ∈ cubeAt c N, ∃ V, IsGoodCluster ω z (wcSubRadius d N) V :=
    fun z hz => hgood z _ (Nat.le_ceil _) hMN ⟨z, fun i => by simp, hz⟩
  choose! V hV using hV
  obtain ⟨p, hp⟩ := exists_walk_of_isGoodCluster_chain hM V hV _ x hx y hy rfl x
    (mem_of_isGoodCluster_of_startsLongPath (hV x hx) hxl) y
    (mem_of_isGoodCluster_of_startsLongPath (hV y hy) hyl)
  refine ⟨p, hp.trans (Nat.mul_le_mul_right _ ?_)⟩
  have hi : ∀ i, (x i - y i).natAbs ≤ 2 * N := fun i => by
    have h1 := hx i; have h2 := hy i
    rw [abs_le] at h1 h2
    omega
  calc ∑ i, (x i - y i).natAbs + 1 ≤ ∑ _i : Fin d, 2 * N + 1 :=
        Nat.add_le_add_right (Finset.sum_le_sum fun i _ => hi i) 1
    _ = 2 * d * N + 1 := by simp [Finset.sum_const]; ring

end Rigidity.Proofs.Section5
