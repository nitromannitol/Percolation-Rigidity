import Rigidity.Steps.Section5.LongNonzeroPaths
import Rigidity.Proofs.S2.JordanCurves
import Rigidity.Proofs.Section5.FiniteMaxPrinciple

/-! # Proposition 5.12: disjoint infinite paths in a component of `L_0`

Carving of Proposition 5.12 (`InfiniteDisjointPathsStmt`, corrected draft L1936-1938, proof
L2093-2122). Let `K = |supp f|`, let `S` be a connected component of `L_0 = {u = 0}` and suppose
that `S` contains `n = K + 3` disjoint infinite paths.

* `ConnectorStep` (connectors and last exits, L2101-2111 with [C22]: the connectors join all the
  initial points): a finite connected `T ⊆ S` and `n` disjoint infinite paths `ρₖ ⊆ S`
  which start in `T` and never return to it.
* `JordanLoopStep` (step:5.12-loop, the one-point compactification, and step:5.12-thick): seen on
  `S²` through a map `σ : ℝ² → S² \ {N}`, the rays and a Jordan loop `α` around `T` satisfy the
  hypotheses of Lemma 2.16; for every component `V` of `S² \ (α ∪ ⋃ γₖ)` whose closure contains
  `N`, a bi-infinite path `π` of the skeleton `T ∪ ⋃ ρₖ` has a complementary side `D` all of whose
  lattice points outside the skeleton are mapped into `V`.
* `TraceCrossingStep` (planar trace): an edge of `𝒞_∞` leaving a complementary component of the
  trace of a lattice path ends on the path.

Glue (step:5.12-jordan, proved below): Lemma 2.16 (`Proofs.S2.jordanCurves`) gives `n` distinct
components `V` with `N` in their closure; since `n > K`, one of them contains no pole. For its
side `D`, a point of `D` with `u > 0` (resp. `u < 0`) lies in a component of `{u > 0}`
(resp. `{-u > 0}`) which stays in `D` (`TraceCrossingStep`: `u = 0` on `π`) and meets a pole by
Lemma 5.17 (`polesSuperLevelSets_of_steps` for `f` and `-f`); that pole is off the skeleton
(`u = 0` there), hence in `V`. So `u = 0` on `𝒞_∞ ∩ D`, which Lemma 5.19 excludes.

Printed issues.
* L2121: the bi-infinite path of the last paragraph is not specified, and `γ_i ∪ α_i ∪ γ_{i+1}`
  is not a lattice path. With `β` the boundary of the half-integer cells of the *filled* connector
  set (L2105), a lattice path of `S` from `γ_i` to `γ_{i+1}` can be forced around a hole of the
  connectors which touches `β` at a concave corner (cells `(1,0), (0,1)` connectors, `(1,1)`
  outside, `(0,0)` a hole enclosed by the ring `(1,0), (1,-1), …, (-1,1), (0,1)`); the hole then
  lies on the side of the bi-infinite path containing `C_i`, and a pole in it breaks
  `u = 0` there. `JordanLoopStep` takes `α` around a spanning tree of the connectors (the boundary
  of a small polygonal regular neighborhood of the tree), which has no holes.
* The proof as printed starts from `K + 2` paths and would bound their number by `K + 1`; the
  statement (and the draft) says at most `K + 2`, which is what is proved here from `K + 3`.
* Lemma 5.14 is not used in step:5.12-loop: the loop is the boundary around the connectors, not a
  loop in an annulus. -/

open MeasureTheory LatticeProb.Percolation Filter Topology

namespace Rigidity.Steps.Section5

open Rigidity.Section5 Rigidity.Section2

variable {ω : Configuration 2}

/-- The skeleton `T ∪ ⋃ₖ ρₖ` of a connector set `T` and rays `ρₖ`. -/
def connectorSkeleton {C : OpenComponent ω} (T : Set C) {n : ℕ} (ρ : Fin n → ℕ → C) : Set C :=
  T ∪ ⋃ k, Set.range (ρ k)

/-- Connectors and last exits (L2101-2111; [C22]: the connectors join all the initial
points): if `S` is connected and contains `n` disjoint infinite paths, then `S` contains a finite
connected set `T` and `n` disjoint infinite paths which start in `T` and never return to it. -/
def ConnectorStep : Prop :=
  ∀ (ω : Configuration 2) (C : OpenComponent ω) (S : Set C), IsConnectedSet C S →
    ∀ n : ℕ, HasDisjointInfinitePaths C S n →
    ∃ T : Set C, T.Finite ∧ T ⊆ S ∧ IsConnectedSet C T ∧
      ∃ ρ : Fin n → ℕ → C, (∀ k, IsInfinitePathIn C S (ρ k)) ∧ (∀ k, ρ k 0 ∈ T) ∧
        (∀ k m, ρ k (m + 1) ∉ T) ∧
        ∀ k l, k ≠ l → Disjoint (Set.range (ρ k)) (Set.range (ρ l))

/-- step:5.12-loop and step:5.12-thick (L2103-2121, [C22]), with the one-point
compactification `σ : ℝ² → S² \ {N}`: for a finite connected `T` and `n ≥ 2` disjoint rays which
start in `T` and never return to it, there are a Jordan loop `α` (around a spanning tree of `T`)
and simple arcs `γₖ` from the last crossing `xₖ` of the `k`-th ray with `α` to `N` (the image of
the ray beyond `xₖ`) satisfying the hypotheses of Lemma 2.16; and for every component `V` of
`S² \ (α ∪ ⋃ γₖ)` whose closure contains `N` (the region between two consecutive rays), there are
a bi-infinite path `π` of the skeleton (the two rays joined through the tree) and a component `D`
of `ℝ² \ π` whose lattice points outside the skeleton are mapped into `V`. -/
def JordanLoopStep : Prop :=
  ∀ (ω : Configuration 2) (C : OpenComponent ω) (T : Set C), T.Finite → IsConnectedSet C T →
    ∀ n : ℕ, 2 ≤ n → ∀ ρ : Fin n → ℕ → C, (∀ k, IsInfinitePathIn C Set.univ (ρ k)) →
      (∀ k, ρ k 0 ∈ T) → (∀ k m, ρ k (m + 1) ∉ T) →
      (∀ k l, k ≠ l → Disjoint (Set.range (ρ k)) (Set.range (ρ l))) →
    ∃ σ : EuclideanSpace ℝ (Fin 2) → S2, IsOpenEmbedding σ ∧ Set.range σ = {northPole}ᶜ ∧
    ∃ (x : Fin n → S2) (γ : ∀ k, Path (x k) northPole) (q : S2) (α : Path q q),
      Function.Injective x ∧ Set.InjOn α (Set.Ico 0 1) ∧ northPole ∉ Set.range α ∧
      (∀ k, Function.Injective (γ k)) ∧ (∀ k, Set.range α ∩ Set.range (γ k) = {x k}) ∧
      (∀ k l, k ≠ l → Set.range (γ k) ∩ Set.range (γ l) = {northPole}) ∧
      ∀ z, z ∉ Set.range α ∪ ⋃ k, Set.range (γ k) →
        northPole ∈ closure (connectedComponentIn (Set.range α ∪ ⋃ k, Set.range (γ k))ᶜ z) →
        ∃ π : ℤ → C, Function.Injective π ∧ (∀ m, (componentGraph C).Adj (π m) (π (m + 1))) ∧
          (∀ m, π m ∈ connectorSkeleton T ρ) ∧ ∃ w ∉ pathTrace π, ∀ y : C,
            latticeEuclideanEmbedding y.val ∈ connectedComponentIn (pathTrace π)ᶜ w →
              σ (latticeEuclideanEmbedding y.val) ∈
                connectedComponentIn (Set.range α ∪ ⋃ k, Set.range (γ k))ᶜ z ∨
              y ∈ connectorSkeleton T ρ

/-- Planar trace of a lattice path: an edge of `𝒞_∞` leaving a connected component of the
complement of the trace of a bi-infinite path `π` ends on `π` (two unit lattice segments meet
only at common endpoints). -/
def TraceCrossingStep : Prop :=
  ∀ (ω : Configuration 2) (C : OpenComponent ω) (π : ℤ → C),
    (∀ m, (componentGraph C).Adj (π m) (π (m + 1))) →
    ∀ (w : EuclideanSpace ℝ (Fin 2)) (y x : C), (componentGraph C).Adj y x →
      latticeEuclideanEmbedding y.val ∈ connectedComponentIn (pathTrace π)ᶜ w →
      latticeEuclideanEmbedding x.val ∉ connectedComponentIn (pathTrace π)ᶜ w →
      ∃ m, x = π m

/-- A property closed under adjacency propagates along walks. -/
theorem walk_propagate {V : Type*} {G : SimpleGraph V} {Q : V → Prop}
    (hQ : ∀ a c, G.Adj a c → Q a → Q c) {a b : V} (p : G.Walk a b) (ha : Q a) : Q b := by
  induction p with
  | nil => exact ha
  | cons h _ ih => exact ih (hQ _ _ h ha)

/-- A connected component of `L` is a connected subset of `L`. -/
theorem isConnectedSet_of_isComponentOf {C : OpenComponent ω} {L S : Set C}
    (h : IsComponentOf C L S) : IsConnectedSet C S ∧ S ⊆ L := by
  obtain ⟨x₀, hx₀, rfl⟩ := h
  have hx₀S : JoinedIn C L x₀ x₀ := ⟨hx₀, hx₀, .refl _⟩
  have key : ∀ y, JoinedIn C L x₀ y → JoinedIn C {y | JoinedIn C L x₀ y} x₀ y := by
    rintro y ⟨_, hy, ⟨p⟩⟩
    have := walk_propagate (Q := fun v : L => ∃ hv : JoinedIn C L x₀ v.1,
        ((componentGraph C).induce {y | JoinedIn C L x₀ y}).Reachable ⟨x₀, hx₀S⟩ ⟨v.1, hv⟩)
      (fun a c hac ⟨ha, hr⟩ => ⟨⟨hx₀, c.2, ha.2.2.trans hac.reachable⟩,
        hr.trans (SimpleGraph.Adj.reachable (G := (componentGraph C).induce _) hac)⟩)
      p ⟨hx₀S, .refl _⟩
    obtain ⟨hv, hr⟩ := this
    exact ⟨hx₀S, hv, hr⟩
  refine ⟨fun y hy y' hy' => ?_, fun y hy => hy.2.1⟩
  obtain ⟨_, hy₁, hr⟩ := key y hy
  obtain ⟨_, hy₁', hr'⟩ := key y' hy'
  exact ⟨hy₁, hy₁', hr.symm.trans hr'⟩

/-- A connected component of `{v > 0}` which meets a side `D` of a bi-infinite path `π` on which
`v = 0` stays in `D` (`TraceCrossingStep`). -/
theorem embed_mem_of_joinedIn (hT : TraceCrossingStep) {C : OpenComponent ω} {π : ℤ → C}
    (hπ : ∀ m, (componentGraph C).Adj (π m) (π (m + 1))) {w : EuclideanSpace ℝ (Fin 2)}
    {A : Set C} (hA : ∀ m, π m ∉ A) {x y : C}
    (hx : latticeEuclideanEmbedding x.val ∈ connectedComponentIn (pathTrace π)ᶜ w)
    (hxy : JoinedIn C A x y) :
    latticeEuclideanEmbedding y.val ∈ connectedComponentIn (pathTrace π)ᶜ w := by
  obtain ⟨hxA, hyA, ⟨p⟩⟩ := hxy
  refine walk_propagate (Q := fun v : A =>
      latticeEuclideanEmbedding v.1.val ∈ connectedComponentIn (pathTrace π)ᶜ w)
    (fun a c hac ha => ?_) p hx
  by_contra hc
  obtain ⟨m, hm⟩ := hT ω C π hπ w a.1 c.1 hac ha hc
  exact hA m (hm ▸ c.2)

/-- Lemma 5.17 on a side `D` of a bi-infinite path on which `v = 0`: a point of `D` with `v > 0`
is joined inside `D ∩ {v > 0}` to a pole. -/
theorem exists_pole_of_mem_side (hT : TraceCrossingStep) {C : OpenComponent ω} {π : ℤ → C}
    (hπ : ∀ m, (componentGraph C).Adj (π m) (π (m + 1))) {w : EuclideanSpace ℝ (Fin 2)}
    {v : C → ℝ} {g : Vertex 2 → ℤ}
    (hP : ∀ T, IsComponentOf C {x | 0 < v x} T → ∃ y ∈ T, g y.val ≠ 0) (hπv : ∀ m, v (π m) = 0)
    {y : C} (hy : latticeEuclideanEmbedding y.val ∈ connectedComponentIn (pathTrace π)ᶜ w)
    (hv : 0 < v y) :
    ∃ y' : C, latticeEuclideanEmbedding y'.val ∈ connectedComponentIn (pathTrace π)ᶜ w ∧
      0 < v y' ∧ g y'.val ≠ 0 := by
  obtain ⟨y', hy', hg⟩ := hP {x | JoinedIn C {x | 0 < v x} y x} ⟨y, hv, rfl⟩
  exact ⟨y', embed_mem_of_joinedIn hT hπ (fun m (hm : 0 < v (π m)) => by
    rw [hπv m] at hm; exact lt_irrefl _ hm) hy hy', hy'.2.1, hg⟩

/-- Proposition 5.12 on a fixed infinite component (deterministic core): given Lemma 5.17 for
`u` and `-u` and the conclusion of Lemma 5.19, no connected component of `L_0` contains
`|supp f| + 3` disjoint infinite paths. -/
theorem false_of_disjointInfinitePaths (hJ : External.JordanCurveTheoremSphere)
    (hC : ConnectorStep) (hL : JordanLoopStep) (hT : TraceCrossingStep) {C : OpenComponent ω}
    {f : Vertex 2 → ℤ} {u : C → ℝ} (hfin : (Function.support f).Finite)
    (hP : ∀ T, IsComponentOf C {x | 0 < u x} T → ∃ y ∈ T, f y.val ≠ 0)
    (hN : ∀ T, IsComponentOf C {x | 0 < (-u) x} T → ∃ y ∈ T, (-f) y.val ≠ 0)
    (hthick : ¬ ∃ π : ℤ → C, Function.Injective π ∧
      (∀ m, (componentGraph C).Adj (π m) (π (m + 1))) ∧ (∀ m, u (π m) = 0) ∧
      ∃ w ∉ pathTrace π, ∀ x : C,
        latticeEuclideanEmbedding x.val ∈ connectedComponentIn (pathTrace π)ᶜ w → u x = 0)
    {S : Set C} (hS : IsComponentOf C (levelSet u 0) S)
    (hpaths : HasDisjointInfinitePaths C S ((Function.support f).ncard + 3)) : False := by
  obtain ⟨hSc, hSL⟩ := isConnectedSet_of_isComponentOf hS
  obtain ⟨T, hTfin, hTS, hTc, ρ, hρ, hρ0, hρT, hρd⟩ := hC ω C S hSc _ hpaths
  have hW : ∀ y ∈ connectorSkeleton T ρ, u y = 0 := by
    rintro y (hy | hy)
    · exact hSL (hTS hy)
    · obtain ⟨k, m, rfl⟩ := Set.mem_iUnion.mp hy
      exact hSL ((hρ k).2.2 m)
  obtain ⟨σ, -, -, x, γ, q, α, hx, hα, hNα, hγ, hαγ, hγγ, hthk⟩ :=
    hL ω C T hTfin hTc _ (by omega) ρ (fun k => ⟨(hρ k).1, (hρ k).2.1, fun _ => trivial⟩)
      hρ0 hρT hρd
  obtain ⟨z, hzΓ, hzne, hzN⟩ :=
    Proofs.S2.jordanCurves hJ _ (by omega) x hx γ q α hα hNα hγ hαγ hγγ
  -- pigeonhole: one of the `|supp f| + 3` components contains no pole
  obtain ⟨k, hk⟩ : ∃ k, ∀ y : C, f y.val ≠ 0 → σ (latticeEuclideanEmbedding y.val) ∉
      connectedComponentIn (Set.range α ∪ ⋃ i, Set.range (γ i))ᶜ (z k) := by
    by_contra hcon
    push Not at hcon
    choose y hy using hcon
    have hinj : Set.InjOn (fun k => (y k).val) Set.univ := by
      intro k _ l _ hkl
      by_contra hne
      apply hzne k l hne
      rw [connectedComponentIn_eq (hy k).2, connectedComponentIn_eq (hy l).2]
      simp only at hkl
      rw [hkl]
    have := Set.ncard_le_ncard_of_injOn (fun k => (y k).val) (fun k _ => (hy k).1) hinj hfin
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at this
    omega
  obtain ⟨π, hπi, hπa, hπW, w, hw, hside⟩ := hthk (z k) (hzΓ k) (hzN k)
  refine hthick ⟨π, hπi, hπa, fun m => hW _ (hπW m), w, hw, fun y hy => ?_⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · obtain ⟨y', hy'D, hy'v, hy'g⟩ := exists_pole_of_mem_side hT hπa hN
      (fun m => by simp [hW _ (hπW m)]) hy (by simpa using hneg)
    rcases hside y' hy'D with h | h
    · exact hk y' (by simpa using hy'g) h
    · simp [hW y' h] at hy'v
  · obtain ⟨y', hy'D, hy'v, hy'g⟩ := exists_pole_of_mem_side hT hπa hP
      (fun m => hW _ (hπW m)) hy hpos
    rcases hside y' hy'D with h | h
    · exact hk y' hy'g h
    · exact (hW y' h ▸ hy'v).false

/-- Proposition 5.12 from Lemma 2.16 (proved, under the Jordan curve theorem on `S²`), Lemma 5.17
(proved from the finite maximum principle and Lemma 5.16), Lemma 5.19 and the planar steps. -/
theorem infiniteDisjointPaths_of_steps {p : unitInterval} {f : Vertex 2 → ℤ}
    (hJ : External.JordanCurveTheoremSphere) (h516 : StrongMaxPrincipleStmt p)
    (h519 : NoThickPathsStmt p f) (hC : ConnectorStep) (hL : JordanLoopStep)
    (hT : TraceCrossingStep) : InfiniteDisjointPathsStmt p f := by
  intro hfin
  have hfin' : (Function.support (-f)).Finite := by rwa [Function.support_neg]
  filter_upwards [polesSuperLevelSets_of_steps Proofs.Section5.finiteMaxPrinciple h516 f hfin,
    polesSuperLevelSets_of_steps Proofs.Section5.finiteMaxPrinciple h516 (-f) hfin',
    h519 hfin] with ω ⟨h, hP⟩ ⟨_, hN⟩ ⟨_, hNT⟩
  refine ⟨h, fun u hu hsupp S hS hpaths => ?_⟩
  have hsupp' : (Function.support (-u)).Infinite := by rwa [Function.support_neg]
  exact false_of_disjointInfinitePaths hJ hC hL hT hfin (hP u hu hsupp 0)
    (hN (-u) (isDecayingPotential_neg hu) hsupp' 0) (fun hex => hNT u hu ⟨hsupp, hex⟩) hS hpaths

end Rigidity.Steps.Section5
