import Rigidity.Steps.Section5.FiniteBranches

/-! # Proposition 5.20: biconnected subsets of a level set

Carving of Proposition 5.20 (`BoundarySizeStmt`, corrected draft L2142-2149, proof L2150-2178).
Let `supp f ⊆ Q_R`, `K = |supp f|`, `M = |Q_{R+1}|` and `C_f = K + 2 + M + 2M² + 2R`
(so `supp f ⊆ Q_{C_f/2}`). Let `S ⊆ L_a` be biconnected, with no pole in the finite components of
`ℤ² \ S`, and suppose that `C_f + 1` disjoint paths `γ_i` connect `S` to infinity.

Glue (proved below):
* step:5.20-exit (L2155, Prop 5.12): at most `K + 2` of the paths stay in `L_a`. For `a ≠ 0`,
  `L_a` is finite (`u → 0`); for `a = 0`, such paths are disjoint infinite paths of the component
  of `L_0` containing `S`. At most `M` paths meet `Q_{R+1}` (they are disjoint).
* step:5.20-neighbours (L2156-2157): on each of the remaining `> 2M²` paths, the last vertex
  `z_i` of the initial stretch in `L_a` is not a pole, so harmonicity gives neighbours `p_i`,
  `n_i` with `u(p_i) > a > u(n_i)`, outside `Q_R`.
* step:5.20-components (L2160-2162, Lemma 5.17): the component `P_i` of `{u > a} \ Q_R`
  containing `p_i` meets `Q_{R+1}` (otherwise it would be a component of `{u > a}` without a
  pole), and likewise `N_i` for `{u < a}`; pigeonhole over `Q_{R+1}²` gives three indices
  `i, j, k` with `P_i = P_j = P_k` and `N_i = N_j = N_k`.
* step:5.20-holes (L2174-2175): by the finite maximum principle, `u = a` on the cluster points of
  every finite component of `ℤ² \ S`, so `P_i` and `N_i` avoid these components.

Step (proved in `Rigidity/Proofs/Section5/ThreeExits.lean`, `threeExitsStep`):
* `ThreeExitsStep` (step:5.20-jordan, L2163-2178, Fig. trisetsoverlap): the three exits are
  impossible in the plane.

Printed issues.
* L2155-2160: `P_i` is the component of `{u_f > a} ∩ (𝒞_∞ \ Q_R)` containing `p_i`, which needs
  `p_i ∉ Q_R`; the paths meeting `Q_{R+1}` (at most `|Q_{R+1}|`) are discarded here, not only
  those meeting `supp f`. The bound on the number of the components `P_i`, `N_i` used by the
  pigeonhole principle (L2162) is not stated; it is Lemma 5.17, as above.
* L2156: the sign normalization `u_f(p_i) > a` is not needed: harmonicity at `z_i` gives
  neighbours on both sides of `a`.
* L2174-2175 (Case 1): the loop "in the level set `L_a`" is built from `S` and from stretches of
  the paths outside `S`, while the hypothesis of the proposition constrains only the finite
  components of `ℤ² \ S`. `ThreeExitsStep` uses this hypothesis only through "`P` and `N` avoid
  the finite components of `ℤ² \ S`". Proof route for it: `S` has at least three vertices and is
  2-connected, so the outer face of the plane graph `S` is bounded by a cycle `O`, and the closed
  disk inside `O` contains `S` and its holes, but no point of `P ∪ N`; cut each stretch after its
  last visit to `S`: three disjoint arcs attached to `O` at distinct points. The interior of the
  disk together with these arcs, `P` and `N` are then three disjoint connected sets joined to
  `z_i, z_j, z_k` by disjoint arcs, a `K_{3,3}` in the plane (Jordan curve theorem on `S²`). -/

open MeasureTheory LatticeProb.Percolation Classical Filter Topology

namespace Rigidity.Steps.Section5

open Rigidity.Section5
open Rigidity.Proofs.Section5 (mem_cube_succ_of_adj joinedIn_trans exists_exit_of_joinedIn
  exists_last_zero)

variable {ω : Configuration 2}

/-- step:5.20-jordan (L2163-2178, Fig. trisetsoverlap), from the Jordan curve theorem on `S²`:
let `S ⊆ L` be biconnected and `P`, `N` connected, the three sets `L`, `P`, `N` pairwise
disjoint, with `P ∪ N` avoiding the finite components of `ℤ² \ S`. There are no three disjoint
stretches `σ_m [0, r_m] ⊆ L` (`m = 0, 1, 2`) from `S` whose last vertices are each adjacent to
both `P` and `N`. (In the proof of Proposition 5.20, `L = L_a`, `P` and `N` are components of
`{u > a} \ Q_R` and `{u < a} \ Q_R`, and the stretches are the initial stretches in `L_a` of three
of the paths.) -/
def ThreeExitsStep : Prop :=
  External.JordanCurveTheoremSphere →
  ∀ (ω : Configuration 2) (C : OpenComponent ω) (S L P N : Set C), IsBiconnected C S → S ⊆ L →
    IsConnectedSet C P → IsConnectedSet C N → Disjoint P N → Disjoint L P → Disjoint L N →
    (∀ x ∈ P ∪ N, ∀ T, IsLatticeComponentOf (Subtype.val '' S)ᶜ T → T.Finite → x.val ∉ T) →
    ∀ (r : Fin 3 → ℕ) (σ : Fin 3 → ℕ → C),
      (∀ m, ∀ t < r m, (componentGraph C).Adj (σ m t) (σ m (t + 1))) →
      (∀ m, σ m 0 ∈ S) → (∀ m, ∀ t ≤ r m, σ m t ∈ L) →
      (∀ m m', m ≠ m' → ∀ t ≤ r m, ∀ t' ≤ r m', σ m t ≠ σ m' t') →
      (∀ m, ∃ y ∈ P, (componentGraph C).Adj (σ m (r m)) y) →
      (∀ m, ∃ y ∈ N, (componentGraph C).Adj (σ m (r m)) y) → False

/-- Being joined inside `S` implies being joined inside any larger set. -/
theorem joinedIn_mono {C : OpenComponent ω} {S L : Set C} {x y : C} (hxy : JoinedIn C S x y)
    (hSL : S ⊆ L) : JoinedIn C L x y := by
  obtain ⟨hx, hy, hr⟩ := hxy
  exact ⟨hSL hx, hSL hy, hr.map (SimpleGraph.induceHomOfLE (G := componentGraph C) hSL).toHom⟩

/-- Two adjacent vertices of `S` are joined inside `S`. -/
theorem joinedIn_of_adj {C : OpenComponent ω} {S : Set C} {x y : C} (hx : x ∈ S) (hy : y ∈ S)
    (hxy : (componentGraph C).Adj x y) : JoinedIn C S x y :=
  ⟨hx, hy, SimpleGraph.Adj.reachable (by simpa using hxy)⟩

/-- An infinite path inside `L` is joined inside `L` to its initial point. -/
theorem joinedIn_of_path {C : OpenComponent ω} {L : Set C} {γ : ℕ → C}
    (hadj : ∀ t, (componentGraph C).Adj (γ t) (γ (t + 1))) (hL : ∀ t, γ t ∈ L) (t : ℕ) :
    JoinedIn C L (γ 0) (γ t) := by
  induction t with
  | zero => exact ⟨hL 0, hL 0, .refl _⟩
  | succ t ih => exact joinedIn_trans ih (joinedIn_of_adj (hL t) (hL (t + 1)) (hadj t))

/-- A lattice component of `A` contains the neighbours in `A` of its points. -/
theorem mem_of_isLatticeComponentOf_adj {A T : Set (Vertex 2)} (hT : IsLatticeComponentOf A T)
    {y z : Vertex 2} (hy : y ∈ T) (hyz : (nearestNeighborGraph 2).Adj y z) (hz : z ∈ A) :
    z ∈ T := by
  obtain ⟨x, -, rfl⟩ := hT
  obtain ⟨hx', hy', hr⟩ := hy
  exact ⟨hx', hz, hr.trans (SimpleGraph.Adj.reachable (by simpa using hyz))⟩

/-- step:5.20-holes: if `-Δu = f` and `f = 0` on a finite component `T` of `ℤ² \ S` with
`S ⊆ L_a`, then `u = a` on the points of `𝒞_∞` in `T` (finite maximum principle for `u` and
`-u`: the outer boundary of `T ∩ 𝒞_∞` lies in `S`). -/
theorem eq_of_mem_finite_hole {C : OpenComponent ω} (huniv : (Set.univ : Set C).Infinite)
    {f : Vertex 2 → ℤ} {u : C → ℝ} (hΔ : ∀ x, -componentLaplacian C u x = f x.val) {a : ℝ}
    {S : Set C} (hSL : S ⊆ levelSet u a) {T : Set (Vertex 2)}
    (hT : IsLatticeComponentOf (Subtype.val '' S)ᶜ T) (hTfin : T.Finite) (hf : ∀ x ∈ T, f x = 0)
    {x : C} (hx : x.val ∈ T) : u x = a := by
  set Ω : Set C := {y | y.val ∈ T}
  have hΩ : Ω.Finite := hTfin.preimage Subtype.val_injective.injOn
  have harm : ∀ y ∈ Ω, componentLaplacian C u y = 0 := fun y hy => by
    have := hΔ y
    rw [hf _ hy] at this
    simpa using this
  have hbd : ∀ y ∈ outerBoundary C Ω, u y = a := by
    rintro y ⟨hyΩ, z, hzΩ, hyz⟩
    by_contra hne
    refine hyΩ (mem_of_isLatticeComponentOf_adj hT hzΩ (openGraph_le ω hyz.symm) ?_)
    rintro ⟨y', hy'S, hy'⟩
    exact hne (by rw [← Subtype.ext hy']; exact hSL hy'S)
  have h1 := Proofs.Section5.finiteMaxPrinciple ω C huniv Ω hΩ u harm a
    (fun y hy => (hbd y hy).le) x hx
  have h2 := Proofs.Section5.finiteMaxPrinciple ω C huniv Ω hΩ (-u)
    (fun y hy => by rw [componentLaplacian_neg, harm y hy, neg_zero]) (-a)
    (fun y hy => by simp [hbd y hy]) x hx
  simp only [Pi.neg_apply, neg_le_neg_iff] at h2
  exact le_antisymm h1 h2

/-- For `a ≠ 0` the level set `L_a` of a function tending to `0` at infinity is finite. -/
theorem levelSet_finite {C : OpenComponent ω} {u : C → ℝ} (hu : Tendsto u cofinite (𝓝 0))
    {a : ℝ} (ha : a ≠ 0) : (levelSet u a).Finite := by
  have h : (u ⁻¹' Metric.ball 0 |a|)ᶜ.Finite :=
    Filter.mem_cofinite.mp (hu (Metric.ball_mem_nhds 0 (abs_pos.mpr ha)))
  refine h.subset fun x hx => ?_
  simp only [levelSet, Set.mem_setOf_eq] at hx
  simp [hx]

/-- step:5.20-exit (L2155, Prop 5.12): among disjoint paths from a connected `S ⊆ L_a` to
infinity, at most `k` stay in `L_a` when a component of `L_0` never contains `k + 1` disjoint
infinite paths. -/
theorem card_stay_le {C : OpenComponent ω} {u : C → ℝ} (hu0 : Tendsto u cofinite (𝓝 0)) {k : ℕ}
    (h512 : ∀ S', IsComponentOf C (levelSet u 0) S' → ¬ HasDisjointInfinitePaths C S' (k + 1))
    {a : ℝ} {S : Set C} (hSL : S ⊆ levelSet u a) (hS : IsConnectedSet C S) {n : ℕ}
    {γ : Fin n → ℕ → C} (hγ : ∀ j, IsInfinitePathIn C Set.univ (γ j) ∧ γ j 0 ∈ S)
    (hd : ∀ j j', j ≠ j' → Disjoint (Set.range (γ j)) (Set.range (γ j'))) :
    (Finset.univ.filter fun j => ∀ t, u (γ j t) = a).card ≤ k := by
  set B := Finset.univ.filter fun j => ∀ t, u (γ j t) = a with hB
  by_contra hlt
  push Not at hlt
  obtain ⟨j₀, hj₀⟩ : B.Nonempty := Finset.card_pos.mp (by omega)
  have hj₀' : ∀ t, u (γ j₀ t) = a := (Finset.mem_filter.mp hj₀).2
  by_cases ha : a = 0
  · subst ha
    have hle : k + 1 ≤ B.card := hlt
    set e : Fin (k + 1) → Fin n := fun i => B.orderEmbOfFin rfl (Fin.castLE hle i)
    have he : Function.Injective e :=
      (B.orderEmbOfFin rfl).injective.comp (Fin.castLE_injective hle)
    have heB : ∀ i t, u (γ (e i) t) = 0 := fun i =>
      (Finset.mem_filter.mp (B.orderEmbOfFin_mem rfl (Fin.castLE hle i))).2
    refine h512 {y | JoinedIn C (levelSet u 0) (γ j₀ 0) y} ⟨γ j₀ 0, hj₀' 0, rfl⟩
      ⟨fun i => γ (e i), fun i => ⟨(hγ (e i)).1.1, (hγ (e i)).1.2.1, fun t => ?_⟩,
        fun i i' hii' => hd _ _ (he.ne hii')⟩
    exact joinedIn_trans (joinedIn_mono (hS _ (hγ j₀).2 _ (hγ (e i)).2) hSL)
      (joinedIn_of_path (hγ (e i)).1.2.1 (heB i) t)
  · exact Set.infinite_range_of_injective (hγ j₀).1.1
      ((levelSet_finite hu0 ha).subset (Set.range_subset_iff.mpr hj₀'))

/-- Disjoint paths meeting a finite set `Q` are at most `|Q|` in number. -/
theorem card_meet_le {C : OpenComponent ω} {n : ℕ} {γ : Fin n → ℕ → C}
    (hd : ∀ j j', j ≠ j' → Disjoint (Set.range (γ j)) (Set.range (γ j')))
    (Q : Set (Vertex 2)) (hQ : Q.Finite) :
    (Finset.univ.filter fun j => ∃ t, (γ j t).val ∈ Q).card ≤ Q.ncard := by
  rw [Set.ncard_eq_toFinset_card Q hQ]
  have h : ∀ j ∈ Finset.univ.filter (fun j => ∃ t, (γ j t).val ∈ Q), ∃ t, (γ j t).val ∈ Q :=
    fun j hj => (Finset.mem_filter.mp hj).2
  choose! τ hτ using h
  refine Finset.card_le_card_of_injOn (fun j => (γ j (τ j)).val) (fun j hj => ?_)
    (fun j _ j' _ hjj' => ?_)
  · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hj
    simp only [Finset.mem_coe, Set.Finite.mem_toFinset]
    exact hτ j (by simpa using hj)
  · by_contra hne
    exact Set.disjoint_left.mp (hd j j' hne) ⟨τ j, rfl⟩ ⟨τ j', (Subtype.ext hjj').symm⟩

/-- step:5.20-neighbours and step:5.20-components (L2156-2162, Lemma 5.17): a path outside
`Q_{R+1}` from `L_a` leaving `L_a` has an initial stretch in `L_a` whose last vertex has
neighbours `p` and `n` joined in `{u > a} \ Q_R` and in `{u < a} \ Q_R` to points of `Q_{R+1}`. -/
theorem exists_exit {C : OpenComponent ω} {f : Vertex 2 → ℤ} {u : C → ℝ}
    (hΔ : ∀ x, -componentLaplacian C u x = f x.val) {a : ℝ}
    (hP : ∀ T, IsComponentOf C {x | a < u x} T → ∃ y ∈ T, f y.val ≠ 0)
    (hN : ∀ T, IsComponentOf C {x | u x < a} T → ∃ y ∈ T, f y.val ≠ 0)
    {R : ℕ} (hR : ∀ x, f x ≠ 0 → x ∈ cube R) {γ : ℕ → C}
    (hadj : ∀ t, (componentGraph C).Adj (γ t) (γ (t + 1))) (h0 : u (γ 0) = a)
    (hexit : ∃ t, u (γ t) ≠ a) (hout : ∀ t, (γ t).val ∉ cube (R + 1)) :
    ∃ r, (∀ t ≤ r, u (γ t) = a) ∧ ∃ p n q q' : C,
      (componentGraph C).Adj (γ r) p ∧ (componentGraph C).Adj (γ r) n ∧
      q.val ∈ cube (R + 1) ∧ q'.val ∈ cube (R + 1) ∧
      JoinedIn C {x | a < u x ∧ x.val ∉ cube R} p q ∧
      JoinedIn C {x | u x < a ∧ x.val ∉ cube R} n q' := by
  obtain ⟨ℓ, hℓ⟩ := hexit
  obtain ⟨r, -, hz, hnz⟩ := exists_last_zero (g := fun t => u (γ t) - a) (by simp [h0])
    (by simpa [sub_eq_zero] using hℓ)
  have hz' : ∀ t ≤ r, u (γ t) = a := fun t ht => by simpa [sub_eq_zero] using hz t ht
  have hf : f (γ r).val = 0 := by
    by_contra h
    exact hout r (cube_mono (Nat.le_succ R) (hR _ h))
  have hlap : componentLaplacian C u (γ r) = 0 := by
    have := hΔ (γ r)
    rw [hf] at this
    simpa using this
  obtain ⟨⟨p, hp, hup⟩, n, hn, hun⟩ :=
    exists_above_below_of_harmonic hlap (hz' r le_rfl) (hadj r) (by simpa [sub_eq_zero] using hnz)
  obtain ⟨y, hyT, hyf⟩ := hP {x | JoinedIn C {x | a < u x} p x} ⟨p, hup, rfl⟩
  obtain ⟨y', hyT', hyf'⟩ := hN {x | JoinedIn C {x | u x < a} n x} ⟨n, hun, rfl⟩
  have hpR : p.val ∉ cube R := fun h => hout r (mem_cube_succ_of_adj hp h)
  have hnR : n.val ∉ cube R := fun h => hout r (mem_cube_succ_of_adj hn h)
  obtain ⟨q, hq, b, hb, hqb⟩ :=
    exists_exit_of_joinedIn (Q := {x : C | x.val ∈ cube R}) hyT hpR (hR _ hyf)
  obtain ⟨q', hq', b', hb', hqb'⟩ :=
    exists_exit_of_joinedIn (Q := {x : C | x.val ∈ cube R}) hyT' hnR (hR _ hyf')
  exact ⟨r, hz', p, n, q, q', hp, hn, mem_cube_succ_of_adj hqb hb, mem_cube_succ_of_adj hqb' hb',
    hq, hq'⟩

/-- Proposition 5.20 on one cluster, given the conclusions of Prop 5.12 and of Lemma 5.17 for
`u` and `-u`: more than `k + M + 2M²` disjoint paths (`M = |Q_{R+1}|`) cannot connect `S` to
infinity. -/
theorem false_of_disjointPathsToInfinity (hJ : External.JordanCurveTheoremSphere)
    (hE : ThreeExitsStep) {C : OpenComponent ω} (huniv : (Set.univ : Set C).Infinite)
    {f : Vertex 2 → ℤ} {u : C → ℝ} (hu : IsDecayingPotential C f u) {R : ℕ}
    (hR : ∀ x, f x ≠ 0 → x ∈ cube R) {k : ℕ}
    (h512 : ∀ S', IsComponentOf C (levelSet u 0) S' → ¬ HasDisjointInfinitePaths C S' (k + 1))
    {a : ℝ} (hP : ∀ T, IsComponentOf C {x | a < u x} T → ∃ y ∈ T, f y.val ≠ 0)
    (hN : ∀ T, IsComponentOf C {x | u x < a} T → ∃ y ∈ T, f y.val ≠ 0)
    {S : Set C} (hSL : S ⊆ levelSet u a) (hS : IsBiconnected C S)
    (hfill : ∀ T, IsLatticeComponentOf (Subtype.val '' S)ᶜ T → T.Finite → ∀ x ∈ T, f x = 0)
    {n : ℕ} (hn : k + (cube (R + 1)).ncard + 2 * ((cube (R + 1)).ncard * (cube (R + 1)).ncard) < n)
    (hpaths : HasDisjointPathsToInfinity C S n) : False := by
  obtain ⟨γ, hγ, hd⟩ := hpaths
  set M := (cube (R + 1)).ncard with hM
  set good := Finset.univ.filter fun j : Fin n =>
    (∃ t, u (γ j t) ≠ a) ∧ ∀ t, (γ j t).val ∉ cube (R + 1) with hgood
  have hcard : 2 * (M * M) < good.card := by
    have h1 := card_stay_le hu.2 h512 hSL hS.1 hγ hd
    have h2 := card_meet_le hd (cube (R + 1)) (cube_finite _)
    have h3 : (Finset.univ : Finset (Fin n)) ⊆ good ∪
        ((Finset.univ.filter fun j => ∀ t, u (γ j t) = a) ∪
          Finset.univ.filter fun j => ∃ t, (γ j t).val ∈ cube (R + 1)) := by
      intro j _
      simp only [hgood, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hs : ∀ t, u (γ j t) = a
      · exact Or.inr (Or.inl hs)
      · by_cases hm : ∃ t, (γ j t).val ∈ cube (R + 1)
        · exact Or.inr (Or.inr hm)
        · push Not at hs hm
          exact Or.inl ⟨hs, hm⟩
    have h4 := (Finset.card_le_card h3).trans (Finset.card_union_le _ _)
    have h5 := Finset.card_union_le (Finset.univ.filter fun j => ∀ t, u (γ j t) = a)
      (Finset.univ.filter fun j => ∃ t, (γ j t).val ∈ cube (R + 1))
    rw [Finset.card_univ, Fintype.card_fin] at h4
    omega
  have key : ∀ j ∈ good, ∃ r, (∀ t ≤ r, u (γ j t) = a) ∧ ∃ p n q q' : C,
      (componentGraph C).Adj (γ j r) p ∧ (componentGraph C).Adj (γ j r) n ∧
      q.val ∈ cube (R + 1) ∧ q'.val ∈ cube (R + 1) ∧
      JoinedIn C {x | a < u x ∧ x.val ∉ cube R} p q ∧
      JoinedIn C {x | u x < a ∧ x.val ∉ cube R} n q' := fun j hj => by
    obtain ⟨hex, hout⟩ := (Finset.mem_filter.mp hj).2
    exact exists_exit hu.1 hP hN hR (hγ j).1.2.1 (hSL (hγ j).2) hex hout
  haveI : Nonempty C := ⟨huniv.nonempty.some⟩
  choose! r hr pp nn q q' hpp hnn hq hq' hpq hnq using key
  obtain ⟨y, -, hy⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to (n := 2)
    (s := good) (t := (cube_finite (R + 1)).toFinset ×ˢ (cube_finite (R + 1)).toFinset)
    (f := fun j => ((q j).val, (q' j).val))
    (fun j hj => by simp [hq j hj, hq' j hj])
    (by rw [Finset.card_product, ← Set.ncard_eq_toFinset_card _ (cube_finite _), ← hM]; linarith)
  obtain ⟨i, hi, j, hj, l, hl, hij, hil, hjl⟩ := Finset.two_lt_card.mp hy
  rw [Finset.mem_filter] at hi hj hl
  obtain ⟨idx, hinj, hgood', hqeq⟩ : ∃ idx : Fin 3 → Fin n, Function.Injective idx ∧
      (∀ m, idx m ∈ good) ∧ ∀ m, q (idx m) = q i ∧ q' (idx m) = q' i := by
    refine ⟨![i, j, l], ?_, fun m => ?_, fun m => ?_⟩
    · intro m m' hmm'
      revert hmm'
      fin_cases m <;> fin_cases m' <;> simp [hij, hil, hjl, hij.symm, hil.symm, hjl.symm]
    · fin_cases m
      exacts [hi.1, hj.1, hl.1]
    · fin_cases m
      · exact ⟨rfl, rfl⟩
      · simp only [Prod.mk.injEq, ← hi.2] at hj
        exact ⟨Subtype.ext hj.2.1, Subtype.ext hj.2.2⟩
      · simp only [Prod.mk.injEq, ← hi.2] at hl
        exact ⟨Subtype.ext hl.2.1, Subtype.ext hl.2.2⟩
  set A := {x : C | a < u x ∧ x.val ∉ cube R}
  set B := {x : C | u x < a ∧ x.val ∉ cube R}
  have hqA : q i ∈ A := (hpq i hi.1).2.1
  have hqB : q' i ∈ B := (hnq i hi.1).2.1
  have hlev : ∀ x : C, x ∈ {y | JoinedIn C A (q i) y} ∪ {y | JoinedIn C B (q' i) y} → u x ≠ a := by
    rintro x (⟨-, ⟨hx, -⟩, -⟩ | ⟨-, ⟨hx, -⟩, -⟩) <;> exact fun h => by rw [h] at hx; exact lt_irrefl _ hx
  refine hE hJ ω C S (levelSet u a) {y | JoinedIn C A (q i) y} {y | JoinedIn C B (q' i) y} hS hSL
    (isConnectedSet_of_isComponentOf ⟨q i, hqA, rfl⟩).1
    (isConnectedSet_of_isComponentOf ⟨q' i, hqB, rfl⟩).1
    (Set.disjoint_left.mpr fun x ⟨_, ⟨hx, _⟩, _⟩ ⟨_, ⟨hx', _⟩, _⟩ => by linarith)
    (Set.disjoint_left.mpr fun x hx hx' => hlev x (Or.inl hx') hx)
    (Set.disjoint_left.mpr fun x hx hx' => hlev x (Or.inr hx') hx)
    (fun x hx T hT hTf hxT => hlev x hx
      (eq_of_mem_finite_hole huniv hu.1 hSL hT hTf (hfill T hT hTf) hxT))
    (fun m => r (idx m)) (fun m => γ (idx m)) (fun m t _ => (hγ (idx m)).1.2.1 t)
    (fun m => (hγ (idx m)).2) (fun m t ht => hr (idx m) (hgood' m) t ht)
    (fun m m' hmm' t _ t' _ heq => Set.disjoint_left.mp (hd _ _ (hinj.ne hmm')) ⟨t, rfl⟩
      ⟨t', heq.symm⟩)
    (fun m => ⟨pp (idx m), joinedIn_symm (by rw [← (hqeq m).1]; exact hpq _ (hgood' m)),
      hpp _ (hgood' m)⟩)
    (fun m => ⟨nn (idx m), joinedIn_symm (by rw [← (hqeq m).2]; exact hnq _ (hgood' m)),
      hnn _ (hgood' m)⟩)

/-- Proposition 5.20 from Lemma 5.16 (through Lemma 5.17, proved from the finite maximum
principle and Lemma 5.16), Proposition 5.12, the Jordan curve theorem on `S²` and
`ThreeExitsStep`. -/
theorem boundarySize_of_steps {p : unitInterval} {f : Vertex 2 → ℤ}
    (hJ : External.JordanCurveTheoremSphere) (h516 : StrongMaxPrincipleStmt p)
    (h512 : InfiniteDisjointPathsStmt p f) (hE : ThreeExitsStep) : BoundarySizeStmt p f := by
  intro hfin
  obtain ⟨R, -, hR⟩ := exists_subset_cube hfin
  have hR' : ∀ x, f x ≠ 0 → x ∈ cube R := fun x hx => hR hx
  obtain ⟨M, hM⟩ : ∃ M, M = (cube (R + 1)).ncard := ⟨_, rfl⟩
  obtain ⟨M2, hM2⟩ : ∃ M2, M2 = 2 * (M * M) := ⟨_, rfl⟩
  refine ⟨(Function.support f).ncard + 2 + M + M2 + 2 * R,
    fun x hx => cube_mono (by omega) (hR' x hx), ?_⟩
  have hfin' : (Function.support (-f)).Finite := by rwa [Function.support_neg]
  filter_upwards [polesSuperLevelSets_of_steps Proofs.Section5.finiteMaxPrinciple h516 f hfin,
    polesSuperLevelSets_of_steps Proofs.Section5.finiteMaxPrinciple h516 (-f) hfin',
    h512 hfin] with ω ⟨h, hP⟩ ⟨_, hN⟩ ⟨_, h12⟩
  refine ⟨h, fun u hu hsupp a S hSL hS hfill hpaths => ?_⟩
  have hsupp' : (Function.support (-u)).Infinite := by rwa [Function.support_neg]
  have hN' : ∀ T, IsComponentOf _ {x | u x < a} T → ∃ y ∈ T, f y.val ≠ 0 := by
    have hset : {x : uniqueInfiniteComponent h | -a < (-u) x} = {x | u x < a} :=
      Set.ext fun x => by simp
    rw [← hset]
    intro T hT
    obtain ⟨y, hy, hy'⟩ := hN (-u) (isDecayingPotential_neg hu) hsupp' (-a) T hT
    exact ⟨y, hy, by simpa using hy'⟩
  refine false_of_disjointPathsToInfinity hJ hE
    (Set.infinite_univ_iff.mpr (Set.infinite_coe_iff.mpr (uniqueInfiniteComponent_infinite h)))
    hu hR' (k := (Function.support f).ncard + 2)
    (fun S' hS' hH => h12 u hu hsupp S' hS' (hasDisjointInfinitePaths_mono hH (by omega)))
    (hP u hu hsupp a) hN' hSL hS hfill ?_ hpaths
  rw [← hM, ← hM2]
  omega

end Rigidity.Steps.Section5
