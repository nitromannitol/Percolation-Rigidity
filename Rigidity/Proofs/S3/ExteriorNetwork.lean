import Rigidity.Steps.S3.SignedIncrement
import Rigidity.Proofs.S3.ExteriorNetworkTrace
import Rigidity.Proofs.S3.ExteriorNetworkProfile
import Rigidity.Proofs.S3.ExteriorNetworkDecay
import Rigidity.Proofs.S3.GreenColumnSublinear
import Rigidity.Proofs.S3.SublinearLiouville
import LatticeProb.External.GreenColumnExistence
import LatticeProb.External.GreenQuantitative

/-!
# The exterior network of the surgery region

`ExteriorNetworkStep p` (`Rigidity/Steps/S3/SignedIncrement.lean`): almost surely the exterior of
the surgery region `U` (the square `Q_2` minus its corners) is a finite network on its sixteen
terminals.

## The route

Let `ω^E` be the environment with every bond meeting `U` closed. Its open components are the
exterior components; by finite energy `ω^E` is typical, so it has a unique infinite cluster `𝒦`,
a corrected plane `ℓ⁰` on `𝒦`, the Liouville property on `𝒦` and Green columns at the terminals of
`𝒦` with the logarithmic asymptotics of Dario and Gu. For every environment `ω'` agreeing with `ω`
off the bonds meeting `U`, the exterior bonds are those of `ω^E`, so each exterior component lies
in one cluster of `ω'`, and the infinite one lies in the infinite cluster `𝒞'`.

* A finite exterior component `X` is a finite network; its trace on the terminals of `X` comes from
  the Dirichlet problem (`exists_traceNetwork_of_finite`).
* On `𝒦`, a corrected plane `ℓ'` of `𝒞'` gives `v = ℓ' - ℓ⁰`, harmonic off the terminals, with
  slope zero, and with zero total flux through the terminals (the flux of `ℓ'` out of `U ∩ 𝒞'`
  vanishes, and so does the flux of each finite exterior component); by the Liouville property `v`
  is a constant plus a zero-sum combination of Green columns, and its response at the terminals is
  the trace network of `exists_traceNetwork_of_green` (uniqueness by the energy identity,
  reciprocity by Green's identity, both with boundary terms `O(n · n^{-3/2})` on the cube
  exhaustion, and the minimum principle).

The conductances are the traces of the exterior components, and the potentials are `ℓ⁰` (extended
by zero off `𝒦`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.Steps.S3
open Rigidity.Proofs.S3.NetworkTrace

namespace Rigidity.Proofs.S3

/-! ### The closed environment -/

/-- The environment with every bond meeting the surgery region closed. -/
noncomputable abbrev closedRegion (ω : Configuration 2) : Configuration 2 :=
  modifyNear surgerySites ∅ ω

theorem meetsSites_bondOfAdjacent_iff {S : Set (Vertex 2)} {x y : Vertex 2}
    (h : (nearestNeighborGraph 2).Adj x y) :
    MeetsSites S (bondOfAdjacent h) ↔ x ∈ S ∨ y ∈ S := by
  simp only [MeetsSites, bondOfAdjacent, Sym2.mem_iff]
  constructor
  · rintro ⟨z, rfl | rfl, hz⟩
    · exact Or.inl hz
    · exact Or.inr hz
  · rintro (hx | hy)
    · exact ⟨x, Or.inl rfl, hx⟩
    · exact ⟨y, Or.inr rfl, hy⟩

theorem modifyNear_of_not_meets {S : Set (Vertex 2)} {F : Set (Bond 2)} {e : Bond 2}
    (he : ¬ MeetsSites S e) (ω : Configuration 2) : modifyNear S F ω e = ω e := by
  simp [modifyNear, he]

theorem closedRegion_adj_iff {ω : Configuration 2} {x y : Vertex 2} :
    (openGraph (closedRegion ω)).Adj x y ↔
      (openGraph ω).Adj x y ∧ x ∉ surgerySites ∧ y ∉ surgerySites := by
  simp only [openGraph_adj_iff]
  constructor
  · rintro ⟨h, ho⟩
    have hm : ¬ MeetsSites surgerySites (bondOfAdjacent h) := fun hm => by
      rw [closedRegion, modifyNear_of_meets hm] at ho
      simp at ho
    rw [closedRegion, modifyNear_of_not_meets hm] at ho
    rw [meetsSites_bondOfAdjacent_iff, not_or] at hm
    exact ⟨⟨h, ho⟩, hm⟩
  · rintro ⟨⟨h, ho⟩, hx, hy⟩
    have hm : ¬ MeetsSites surgerySites (bondOfAdjacent h) := by
      rw [meetsSites_bondOfAdjacent_iff, not_or]; exact ⟨hx, hy⟩
    exact ⟨h, by rw [closedRegion, modifyNear_of_not_meets hm]; exact ho⟩

theorem agree_adj_iff {ω ω' : Configuration 2}
    (hω' : ∀ e, ¬ MeetsSites surgerySites e → ω' e = ω e) {x y : Vertex 2}
    (hx : x ∉ surgerySites) (hy : y ∉ surgerySites) :
    (openGraph ω').Adj x y ↔ (openGraph ω).Adj x y := by
  simp only [openGraph_adj_iff]
  have hm : ∀ h : (nearestNeighborGraph 2).Adj x y,
      ¬ MeetsSites surgerySites (bondOfAdjacent h) := fun h hm => by
    rcases (meetsSites_bondOfAdjacent_iff h).1 hm with h1 | h1
    · exact hx h1
    · exact hy h1
  exact ⟨fun ⟨h, ho⟩ => ⟨h, by rwa [← hω' _ (hm h)]⟩,
    fun ⟨h, ho⟩ => ⟨h, by rwa [hω' _ (hm h)]⟩⟩

theorem closedRegion_le {ω ω' : Configuration 2}
    (hω' : ∀ e, ¬ MeetsSites surgerySites e → ω' e = ω e) :
    openGraph (closedRegion ω) ≤ openGraph ω' := fun _ _ h => by
  obtain ⟨h1, hx, hy⟩ := closedRegion_adj_iff.1 h
  exact (agree_adj_iff hω' hx hy).2 h1

/-- A site outside the region which is not a terminal has no lattice neighbour in the region. -/
theorem not_mem_sites_of_adj {x y : Vertex 2} (hx : x ∉ surgerySites)
    (hxT : x ∉ surgeryTerminals) (hadj : (nearestNeighborGraph 2).Adj x y) :
    y ∉ surgerySites := fun hy => by
  rcases site_or_terminal_of_mem_nearSites (mem_nearSites_of_adj hy hadj.symm) with h | h
  · exact hx h
  · exact hxT h

/-- The sites of the region are isolated in the closed environment. -/
theorem eq_of_reachable_closedRegion {ω : Configuration 2} {x y : Vertex 2}
    (hx : x ∈ surgerySites) (h : (openGraph (closedRegion ω)).Reachable x y) : x = y := by
  obtain ⟨p⟩ := h
  cases p with
  | nil => rfl
  | cons hadj _ => exact absurd hx (closedRegion_adj_iff.1 hadj).2.1

/-- A component of a subgraph lies in the component of the larger graph of any of its points. -/
theorem supp_subset_of_le {V : Type*} {G H : SimpleGraph V} (hGH : G ≤ H)
    (X : G.ConnectedComponent) {x : V} (hx : x ∈ X.supp) :
    X.supp ⊆ (H.connectedComponentMk x).supp := by
  intro y hy
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hx hy ⊢
  exact SimpleGraph.ConnectedComponent.sound
    ((SimpleGraph.ConnectedComponent.exact (hy.trans hx.symm)).mono hGH)

/-! ### Neighbour sums -/

/-- A neighbour sum on a cluster is the neighbour sum of the open graph. -/
theorem sum_component_neighbor {η : Configuration 2} (C : OpenComponent η) (x : C)
    (H : Vertex 2 → ℝ) :
    ∑ y ∈ (componentGraph C).neighborFinset x, H y.val =
      ∑ y ∈ (openGraph η).neighborFinset x.val, H y := by
  have e : (openGraph η).neighborFinset x.val =
      ((componentGraph C).neighborFinset x).map (Function.Embedding.subtype _) := by
    ext y
    simp only [Finset.mem_map, SimpleGraph.mem_neighborFinset, Function.Embedding.coe_subtype]
    constructor
    · intro hadj
      exact ⟨⟨y, C.mem_supp_of_adj_mem_supp x.2 hadj⟩, hadj, rfl⟩
    · rintro ⟨y', hadj, rfl⟩
      exact hadj
  rw [e, Finset.sum_map]
  rfl

/-- The Laplacian on a cluster is the Laplacian of the open graph. -/
theorem lap_component {η : Configuration 2} (C : OpenComponent η) (F : Vertex 2 → ℝ) (x : C) :
    lap (componentGraph C) (fun y => F y.val) x = lap (openGraph η) F x.val :=
  sum_component_neighbor C x (fun y => F y - F x.val)

open scoped Classical in
/-- The exterior neighbours of a site outside the region. -/
theorem neighborFinset_closedRegion {ω ω' : Configuration 2}
    (hω' : ∀ e, ¬ MeetsSites surgerySites e → ω' e = ω e) {t : Vertex 2}
    (ht : t ∉ surgerySites) :
    (openGraph (closedRegion ω)).neighborFinset t =
      ((openGraph ω').neighborFinset t).filter (· ∉ surgerySites) := by
  ext y
  simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset, closedRegion_adj_iff]
  constructor
  · rintro ⟨h, -, hy⟩; exact ⟨(agree_adj_iff hω' ht hy).2 h, hy⟩
  · rintro ⟨h, hy⟩; exact ⟨(agree_adj_iff hω' ht hy).1 h, ht, hy⟩

/-- Exchanging the order of a double sum over adjacent pairs. -/
theorem sum_sum_filter_comm {V : Type*} [DecidableEq V] (G : SimpleGraph V) [G.LocallyFinite]
    (A P : Finset V) (H : V → V → ℝ) :
    ∑ x ∈ A, ∑ y ∈ (G.neighborFinset x).filter (· ∈ P), H x y =
      ∑ y ∈ P, ∑ x ∈ (G.neighborFinset y).filter (· ∈ A), H x y := by
  classical
  have h1 : ∀ x, ∑ y ∈ (G.neighborFinset x).filter (· ∈ P), H x y =
      ∑ y ∈ P, if G.Adj x y then H x y else 0 := by
    intro x
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext y
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset, and_comm]
  have h2 : ∀ y, ∑ x ∈ (G.neighborFinset y).filter (· ∈ A), H x y =
      ∑ x ∈ A, if G.Adj x y then H x y else 0 := by
    intro y
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext x
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset, SimpleGraph.adj_comm,
      and_comm]
  simp_rw [h1, h2]
  exact Finset.sum_comm

/-- An antisymmetric double sum over a finite set vanishes. -/
theorem sum_sum_antisymm_eq_zero {ι : Type*} (Q : Finset ι) (H : ι → ι → ℝ)
    (hH : ∀ t s, H s t = -H t s) : ∑ t ∈ Q, ∑ s ∈ Q, H t s = 0 := by
  have h : ∑ t ∈ Q, ∑ s ∈ Q, H t s = -∑ t ∈ Q, ∑ s ∈ Q, H t s := by
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun b _ => hH a b
  linarith

open scoped Classical in
/-- **No net current through the region**: for a function harmonic on a cluster `D` of `ω'`, the
total exterior current at the terminals of `D` vanishes (the flux out of `U ∩ D` is zero, and
every bond from `U ∩ D` out of `U` ends at a terminal). -/
theorem sum_exterior_current_eq_zero {ω' : Configuration 2} (D : OpenComponent ω')
    (F : Vertex 2 → ℝ) (hF : ∀ x ∈ D.supp, lap (openGraph ω') F x = 0) :
    ∑ t ∈ surgeryTerminals.filter (· ∈ D.supp),
      ∑ y ∈ ((openGraph ω').neighborFinset t).filter (· ∉ surgerySites), (F y - F t) = 0 := by
  set G' := openGraph ω'
  set P := surgeryTerminals.filter (· ∈ D.supp) with hP
  set A := nearSites.filter (fun x => x ∈ surgerySites ∧ x ∈ D.supp) with hA
  have hmemA : ∀ x, x ∈ A ↔ x ∈ surgerySites ∧ x ∈ D.supp := fun x => by
    rw [hA, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨mem_nearSites_of_site h.1, h⟩⟩
  -- the flux out of `A`
  have h0 : ∑ x ∈ A, lap G' F x = 0 :=
    Finset.sum_eq_zero fun x hx => hF x ((hmemA x).1 hx).2
  rw [sum_lap_eq_boundary] at h0
  have hbd : ∀ x ∈ A, (G'.neighborFinset x).filter (· ∉ A) = (G'.neighborFinset x).filter (· ∈ P) := by
    intro x hx
    obtain ⟨hxU, hxD⟩ := (hmemA x).1 hx
    ext y
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset, hP, hmemA]
    refine and_congr_right fun hadj => ?_
    have hyD : y ∈ D.supp := D.mem_supp_of_adj_mem_supp hxD hadj
    constructor
    · intro hy
      have hyU : y ∉ surgerySites := fun h => hy ⟨h, hyD⟩
      refine ⟨?_, hyD⟩
      rcases site_or_terminal_of_mem_nearSites
        (mem_nearSites_of_adj hxU (openGraph_le ω' hadj)) with h | h
      · exact absurd h hyU
      · exact h
    · rintro ⟨hyT, -⟩ ⟨hyU, -⟩
      exact not_mem_surgerySites_of_mem_terminals hyT hyU
  rw [Finset.sum_congr rfl fun x hx => by rw [hbd x hx], sum_sum_filter_comm] at h0
  have hin : ∀ t ∈ P, (G'.neighborFinset t).filter (· ∈ A) =
      (G'.neighborFinset t).filter (· ∈ surgerySites) := by
    intro t ht
    have htD : t ∈ D.supp := (Finset.mem_filter.1 ht).2
    ext y
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset, hmemA]
    refine and_congr_right fun hadj => ?_
    exact ⟨fun h => h.1, fun h => ⟨h, D.mem_supp_of_adj_mem_supp htD hadj⟩⟩
  rw [Finset.sum_congr rfl fun t ht => by rw [hin t ht]] at h0
  -- harmonicity at the terminals splits the current
  have hsplit : ∀ t ∈ P,
      ∑ y ∈ (G'.neighborFinset t).filter (· ∉ surgerySites), (F y - F t) =
        ∑ y ∈ (G'.neighborFinset t).filter (· ∈ surgerySites), (F t - F y) := by
    intro t ht
    have h := hF t (Finset.mem_filter.1 ht).2
    rw [lap, ← Finset.sum_filter_add_sum_filter_not _ (· ∈ surgerySites)] at h
    have e : ∑ y ∈ (G'.neighborFinset t).filter (· ∈ surgerySites), (F t - F y) =
        -∑ y ∈ (G'.neighborFinset t).filter (· ∈ surgerySites), (F y - F t) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [e]
    linarith
  rw [Finset.sum_congr rfl hsplit]
  exact h0

/-! ### The network of an exterior component -/

/-- The functions with slope zero on a cluster. -/
def slopeZeroSubmodule {η : Configuration 2} (C : OpenComponent η) : Submodule ℝ (C → ℝ) where
  carrier := {v | componentSlopeAsymptotics C 0 v}
  add_mem' {u v} hu hv := by simpa using componentSlopeAsymptotics_add C hu hv
  zero_mem' := (isCorrectedPlane_const C 0).2
  smul_mem' a v hv := by simpa using componentSlopeAsymptotics_smul C hv a

open scoped Classical in
/-- `c` is a network of the component `X` on the terminals, for the admissible potentials `Adm`:
symmetric nonnegative conductances between terminals of `X`, of total at most `4` at each site, with
Kirchhoff's law at the terminals of `X` for every admissible potential harmonic at the other sites
of `X`. -/
def IsComponentNetwork {η : Configuration 2} (X : OpenComponent η) (Adm : (X → ℝ) → Prop)
    (c : Vertex 2 → Vertex 2 → ℝ) : Prop :=
  (∀ t s, c t s = c s t) ∧ (∀ t s, 0 ≤ c t s) ∧ (∀ t, ∑ s ∈ surgeryTerminals, c t s ≤ 4) ∧
    (∀ t s, c t s ≠ 0 → t ∈ X.supp ∧ s ∈ X.supp) ∧
    ∀ f : X → ℝ, Adm f →
      (∀ x : X, x.val ∉ surgeryTerminals → lap (componentGraph X) f x = 0) →
      ∀ t : X, t.val ∈ surgeryTerminals →
        lap (componentGraph X) f t =
          ∑ s ∈ surgeryTerminals, c t s * (Rigidity.Section3.extend X f s - f t)

open scoped Classical in
/-- A trace network of the component graph on the terminals of `X`, as a network indexed by the
sites of the lattice. -/
theorem isComponentNetwork_of_trace {η : Configuration 2} (X : OpenComponent η)
    (Adm : (X → ℝ) → Prop) (c' : X → X → ℝ)
    (hc' : IsTraceNetwork (componentGraph X) (surgeryTerminals.subtype (· ∈ X)) c')
    (hK : ∀ f : X → ℝ, Adm f →
      (∀ x, x ∉ surgeryTerminals.subtype (· ∈ X) → lap (componentGraph X) f x = 0) →
      ∀ t ∈ surgeryTerminals.subtype (· ∈ X), lap (componentGraph X) f t =
        ∑ s ∈ surgeryTerminals.subtype (· ∈ X), c' t s * (f s - f t)) :
    IsComponentNetwork X Adm
      (fun t s => if h : t ∈ X.supp ∧ s ∈ X.supp then c' ⟨t, h.1⟩ ⟨s, h.2⟩ else 0) := by
  obtain ⟨hsym, hnn, hrow, -⟩ := hc'
  have hsum : ∀ H : X → ℝ, ∑ s ∈ surgeryTerminals, (if h : s ∈ X.supp then H ⟨s, h⟩ else 0) =
      ∑ s ∈ surgeryTerminals.subtype (· ∈ X), H s := by
    intro H
    have e1 := Finset.sum_subtype_eq_sum_filter (s := surgeryTerminals) (p := (· ∈ X))
      (fun s => if h : s ∈ X.supp then H ⟨s, h⟩ else 0)
    rw [Finset.sum_filter_of_ne (fun x _ hx => by by_contra h; exact hx (dif_neg h))] at e1
    rw [← e1]
    exact Finset.sum_congr rfl fun x _ => by
      rw [dif_pos (show (x : Vertex 2) ∈ X.supp from x.2)]
  refine ⟨fun t s => ?_, fun t s => ?_, fun t => ?_, fun t s h => ?_, ?_⟩
  · dsimp only
    by_cases h : t ∈ X.supp ∧ s ∈ X.supp
    · rw [dif_pos h, dif_pos ⟨h.2, h.1⟩, hsym]
    · rw [dif_neg h, dif_neg fun h' => h ⟨h'.2, h'.1⟩]
  · simp only
    split_ifs
    · exact hnn _ _
    · exact le_rfl
  · by_cases ht : t ∈ X.supp
    · have e : ∑ s ∈ surgeryTerminals,
          (if h : t ∈ X.supp ∧ s ∈ X.supp then c' ⟨t, h.1⟩ ⟨s, h.2⟩ else 0) =
          ∑ s ∈ surgeryTerminals.subtype (· ∈ X), c' ⟨t, ht⟩ s := by
        rw [← hsum]
        refine Finset.sum_congr rfl fun s _ => ?_
        by_cases hs : s ∈ X.supp
        · rw [dif_pos ⟨ht, hs⟩, dif_pos hs]
        · rw [dif_neg fun h => hs h.2, dif_neg hs]
      simp only
      rw [e]
      have hdeg : (componentGraph X).degree ⟨t, ht⟩ ≤ 4 := componentGraph_degree_le X _
      exact (hrow _).trans (by exact_mod_cast hdeg)
    · simp only [ht, false_and, dite_false, Finset.sum_const_zero]
      norm_num
  · by_contra hn
    exact h (dif_neg hn)
  · intro f hf hharm t ht
    rw [hK f hf (fun x hx => hharm x (by simpa using hx)) t (by simpa using ht), ← hsum]
    refine Finset.sum_congr rfl fun s _ => ?_
    dsimp only
    have ht' : (t : Vertex 2) ∈ X.supp := t.2
    by_cases hs : s ∈ X.supp
    · rw [dif_pos hs, dif_pos ⟨ht', hs⟩, extend_of_mem f hs]
    · rw [dif_neg hs, dif_neg fun h => hs h.2, zero_mul]

open scoped Classical in
/-- The network of a finite exterior component (the Dirichlet problem). -/
theorem exists_componentNetwork_of_finite {η : Configuration 2} (X : OpenComponent η)
    (hX : X.supp.Finite) (Adm : (X → ℝ) → Prop) : ∃ c, IsComponentNetwork X Adm c := by
  haveI : Fintype X := hX.fintype
  obtain ⟨c', hc', hK⟩ := exists_traceNetwork_of_finite (componentGraph X)
    X.connected_toSimpleGraph (surgeryTerminals.subtype (· ∈ X))
  exact ⟨_, isComponentNetwork_of_trace X Adm c' hc' fun f _ hf t ht => hK f hf t ht⟩

/-- The typical properties of the closed environment used for the exterior network: a unique
infinite cluster with a corrected plane, the Liouville property, and Green columns at the
terminals with the logarithmic asymptotics of Dario and Gu (error `O(|x - r|^{-3/4})`). -/
structure ExteriorTypical (η : Configuration 2) : Prop where
  unique : HasUniqueInfiniteOpenComponent η
  plane : ∃ l, IsCorrectedPlane (uniqueInfiniteComponent unique) (Pi.single 0 1) l
  liouville : ∀ v : uniqueInfiniteComponent unique → ℝ,
    (∀ x, componentLaplacian (uniqueInfiniteComponent unique) v x = 0) →
    componentSlopeAsymptotics (uniqueInfiniteComponent unique) 0 v → ∃ c, ∀ x, v x = c
  green : ∃ κ : ℝ, 0 < κ ∧ ∀ r : uniqueInfiniteComponent unique, r.val ∈ surgeryTerminals →
    ∃ (g : uniqueInfiniteComponent unique → ℝ) (Kc M A : ℝ),
      IsGreenColumn 2 le_rfl (uniqueInfiniteComponent unique) r g ∧
      ∀ x, x ≠ r → M ≤ ‖latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding r.val‖ →
        |g x + Real.log ‖latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding r.val‖ /
            (2 * Real.pi * κ) - Kc| ≤
          A / ‖latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding r.val‖ ^ (3 / 4 : ℝ)

open scoped Classical in
/-- The admissible potentials of an exterior component: on the infinite one, slope zero and zero
total flux through the terminals. -/
def ExteriorAdmissible {η : Configuration 2} (X : OpenComponent η) (f : X → ℝ) : Prop :=
  X.supp.Infinite → componentSlopeAsymptotics X 0 f ∧
    ∑ t ∈ surgeryTerminals.subtype (· ∈ X), lap (componentGraph X) f t = 0

open scoped Classical in
/-- The network of the infinite exterior component (Green columns and the Liouville property). -/
theorem exists_componentNetwork_of_infinite {η : Configuration 2} (hη : ExteriorTypical η) :
    ∃ c, IsComponentNetwork (uniqueInfiniteComponent hη.unique)
      (ExteriorAdmissible (uniqueInfiniteComponent hη.unique)) c := by
  set K := uniqueInfiniteComponent hη.unique
  set TX := surgeryTerminals.subtype (· ∈ K)
  obtain ⟨κ, hκ, hgreen⟩ := hη.green
  choose! gf Kf Mf Af hgf hasym using hgreen
  have hg : ∀ r ∈ TX, ∀ x, lap (componentGraph K) (gf r) x = -(if x = r then 1 else 0) := by
    intro r hr x
    have h1 := (hgf r (Finset.mem_subtype.1 hr)).1 x
    have h2 : componentLaplacian K (gf r) x = lap (componentGraph K) (gf r) x := rfl
    linarith
  have hdecay : ∀ b : TX → ℝ, ∑ r, b r = 0 →
      ∃ C, ∀ x, |∑ r, b r * (gf r x - Kf r)| ≤
        C * (1 + ‖latticeEuclideanEmbedding x.val‖) ^ (-(3 / 4 : ℝ)) :=
    fun b hb => greenCombination_decay K TX gf Kf κ hκ
      (fun r hr => ⟨Mf r, Af r, hasym r (Finset.mem_subtype.1 hr)⟩) b hb
  obtain ⟨c', hc', hK⟩ := exists_traceNetwork_of_green (componentGraph K)
    K.connected_toSimpleGraph hg Kf (fun x => (1 + ‖latticeEuclideanEmbedding x.val‖) ^ (-(3 / 4 : ℝ)))
    (fun x => by positivity) (profile_finite K) (profile_boundary K) hdecay
    (slopeZeroSubmodule K)
    (fun r hr => componentSlopeAsymptotics_zero_of_tail K (gf r)
      ((hgf r (Finset.mem_subtype.1 hr)).2.1 rfl).2)
    (fun v hv h => hη.liouville v h hv)
  refine ⟨_, isComponentNetwork_of_trace K _ c' hc' fun f hf hharm t ht => ?_⟩
  obtain ⟨hf1, hf2⟩ := hf (uniqueInfiniteComponent_infinite hη.unique)
  exact hK f hf1 hharm hf2 t ht

/-- **The network of every exterior component.** -/
theorem exists_componentNetwork {η : Configuration 2} (hη : ExteriorTypical η)
    (X : OpenComponent η) : ∃ c, IsComponentNetwork X (ExteriorAdmissible X) c := by
  by_cases hX : X.supp.Finite
  · exact exists_componentNetwork_of_finite X hX _
  · obtain rfl := (eq_uniqueInfiniteComponent_iff hη.unique X).2 hX
    exact exists_componentNetwork_of_infinite hη

/-! ### Assembly -/

theorem sum_component_neighbor_filter {η : Configuration 2} (C : OpenComponent η) (x : C)
    (P : Vertex 2 → Prop) [DecidablePred P] (H : Vertex 2 → ℝ) :
    ∑ y ∈ ((componentGraph C).neighborFinset x).filter (fun y => P y.val), H y.val =
      ∑ y ∈ ((openGraph η).neighborFinset x.val).filter P, H y := by
  rw [Finset.sum_filter, Finset.sum_filter]
  exact sum_component_neighbor C x (fun y => if P y then H y else 0)

theorem componentSlopeAsymptotics_restrict {η η' : Configuration 2} (C : OpenComponent η)
    (D : OpenComponent η') (hCD : C.supp ⊆ D.supp) {p : Fin 2 → ℝ} {u : D → ℝ}
    (hu : componentSlopeAsymptotics D p u) :
    componentSlopeAsymptotics C p (fun x => u ⟨x.val, hCD x.2⟩) := by
  intro ε hε
  obtain ⟨R0, hR0, h⟩ := hu ε hε
  refine ⟨R0, hR0, fun R hR x hx => ?_⟩
  have hx' : (⟨x.val, hCD x.2⟩ : D) ∈ componentEuclideanBall D 0 R := by
    rw [mem_componentEuclideanBall] at hx ⊢
    exact hx
  exact h R hR _ hx'

theorem lap_sub_fun {V : Type*} (G : SimpleGraph V) [G.LocallyFinite] (F H : V → ℝ) (x : V) :
    lap G (fun z => F z - H z) x = lap G F x - lap G H x := by
  simp only [lap, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

open scoped Classical in
/-- **The exterior network of a typical closed environment**: the conductances are the traces of
the exterior components on their terminals, the potentials the corrected plane of the infinite
exterior component. -/
theorem exteriorNetworkAt_of_typical {ω : Configuration 2}
    (hη : ExteriorTypical (closedRegion ω)) :
    ∃ (c : Vertex 2 → Vertex 2 → ℝ) (l0 : Vertex 2 → ℝ), ExteriorNetworkAt ω c l0 := by
  obtain ⟨ℓ0, hℓ0⟩ := hη.plane
  have hKinf := uniqueInfiniteComponent_infinite hη.unique
  have hKuniq : ∀ X : OpenComponent (closedRegion ω), X.supp.Infinite →
      X = uniqueInfiniteComponent hη.unique :=
    fun X hX => (eq_uniqueInfiniteComponent_iff hη.unique X).2 hX
  generalize uniqueInfiniteComponent hη.unique = K at ℓ0 hℓ0 hKinf hKuniq
  choose cX hcX using fun X : OpenComponent (closedRegion ω) => exists_componentNetwork hη X
  obtain ⟨comp, hcomp⟩ : ∃ comp : Vertex 2 → OpenComponent (closedRegion ω),
      ∀ x, comp x = (openGraph (closedRegion ω)).connectedComponentMk x := ⟨_, fun _ => rfl⟩
  have hmem : ∀ x, x ∈ (comp x).supp := fun x => by
    rw [hcomp]; exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).2 rfl
  have hcomp_of_mem : ∀ {X : OpenComponent (closedRegion ω)} {x : Vertex 2}, x ∈ X.supp →
      comp x = X := fun hx => by
    rw [hcomp]; exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hx
  have hreach : ∀ x y, comp x = comp y → (openGraph (closedRegion ω)).Reachable x y :=
    fun x y h => by rw [hcomp, hcomp] at h; exact SimpleGraph.ConnectedComponent.exact h
  have hsupp' : ∀ t s, cX (comp t) t s ≠ 0 → comp s = comp t := fun t s h =>
    hcomp_of_mem ((hcX (comp t)).2.2.2.1 t s h).2
  have hsymc : ∀ t s, cX (comp t) t s = cX (comp s) s t := by
    intro t s
    by_cases h : comp t = comp s
    · rw [h]; exact (hcX (comp s)).1 t s
    · have h1 : cX (comp t) t s = 0 := by
        by_contra h1; exact h (hsupp' t s h1).symm
      have h2 : cX (comp s) s t = 0 := by
        by_contra h2; exact h (hsupp' s t h2)
      rw [h1, h2]
  set l0 := Rigidity.Section3.extend K ℓ0 with hl0
  have hl0K : ∀ x (hx : x ∈ K.supp), l0 x = ℓ0 ⟨x, hx⟩ := fun x hx => extend_of_mem ℓ0 hx
  have hl0zero : ∀ x, comp x ≠ K → l0 x = 0 := fun x hx => by
    simp only [hl0, Rigidity.Section3.extend]
    rw [dif_neg fun h => hx (hcomp_of_mem h)]
  have hlapl0 : ∀ x, lap (openGraph (closedRegion ω)) l0 x = 0 := by
    intro x
    by_cases hx : x ∈ K.supp
    · rw [← lap_component K _ ⟨x, hx⟩]
      have e : (fun y : K => l0 y.val) = ℓ0 := funext fun y => extend_of_mem ℓ0 y.2
      rw [e]
      obtain ⟨hlap0, -⟩ := hℓ0.1
      exact hlap0 ⟨x, hx⟩
    · have hx' : comp x ≠ K := fun h => hx (by rw [← h]; exact hmem x)
      rw [lap]
      refine Finset.sum_eq_zero fun y hy => ?_
      have hy' : comp y = comp x := hcomp_of_mem ((comp x).mem_supp_of_adj_mem_supp (hmem x)
        ((SimpleGraph.mem_neighborFinset _ _ _).1 hy))
      rw [hl0zero y (by rw [hy']; exact hx'), hl0zero x hx', sub_self]
  refine ⟨fun t s => cX (comp t) t s, l0, hsymc, fun t s => (hcX (comp t)).2.1 t s,
    fun t => (hcX (comp t)).2.2.1 t, ?_⟩
  intro ω' hω' h'
  have hDinf := uniqueInfiniteComponent_infinite h'
  have hDuniq : ∀ X : OpenComponent ω', X.supp.Infinite → X = uniqueInfiniteComponent h' :=
    fun X hX => (eq_uniqueInfiniteComponent_iff h' X).2 hX
  generalize uniqueInfiniteComponent h' = D at hDinf hDuniq ⊢
  have hle := closedRegion_le hω'
  have hsubD : ∀ x ∈ D.supp, (comp x).supp ⊆ D.supp := by
    intro x hx
    have h1 := supp_subset_of_le hle (comp x) (hmem x)
    have h2 : (openGraph ω').connectedComponentMk x = D :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hx
    rwa [h2] at h1
  have hKD : K.supp ⊆ D.supp := by
    obtain ⟨k, hk⟩ := hKinf.nonempty
    have h1 := supp_subset_of_le hle K hk
    rwa [hDuniq _ (hKinf.mono h1)] at h1
  refine ⟨fun t _ s _ h => ?_, fun t _ s _ h => ?_, ?_⟩
  · -- conductances join terminals of one exterior component, hence of one cluster of `ω'`
    have e := hsupp' t s h
    constructor
    · intro ht; exact hsubD t ht (by rw [← e]; exact hmem s)
    · intro hs; exact hsubD s hs (by rw [e]; exact hmem t)
  · -- electromotive forces only on the infinite exterior component
    have hc : cX (comp t) t s ≠ 0 := left_ne_zero_of_mul h
    have hd := right_ne_zero_of_mul h
    by_cases htK : comp t = K
    · exact hKD (by rw [← htK]; exact hmem t)
    · exfalso
      have hsK : comp s ≠ K := by rw [hsupp' t s hc]; exact htK
      exact hd (by rw [hl0zero s hsK, hl0zero t htK, sub_zero])
  -- Kirchhoff's law
  intro u' hu' t htT htD
  beta_reduce
  obtain ⟨hharm', -⟩ := hu'.1
  have hFv : ∀ z (hz : z ∈ D.supp), Rigidity.Section3.extend D u' z = u' ⟨z, hz⟩ :=
    fun z hz => extend_of_mem u' hz
  have hFharm : ∀ x ∈ D.supp, lap (openGraph ω') (Rigidity.Section3.extend D u') x = 0 := by
    intro x hx
    rw [← lap_component D _ ⟨x, hx⟩]
    have e : (fun y : D => Rigidity.Section3.extend D u' y.val) = u' :=
      funext fun y => hFv y.val y.2
    rw [e]
    exact hharm' ⟨x, hx⟩
  set F := Rigidity.Section3.extend D u' with hF
  have hext : ∀ x, x ∉ surgerySites → lap (openGraph (closedRegion ω)) F x =
      ∑ y ∈ ((openGraph ω').neighborFinset x).filter (· ∉ surgerySites), (F y - F x) := by
    intro x hx
    rw [lap, neighborFinset_closedRegion hω' hx]
  have hharmX : ∀ x, x ∈ D.supp → x ∉ surgerySites → x ∉ surgeryTerminals →
      lap (openGraph (closedRegion ω)) F x = 0 := by
    intro x hxD hxU hxT
    rw [hext x hxU, Finset.filter_true_of_mem fun y hy =>
      not_mem_sites_of_adj hxU hxT (openGraph_le ω' ((SimpleGraph.mem_neighborFinset _ _ _).1 hy))]
    exact hFharm x hxD
  have hlapfX : ∀ (X : OpenComponent (closedRegion ω)) (x : X),
      lap (componentGraph X) (fun x => F x.val - l0 x.val) x =
        lap (openGraph (closedRegion ω)) F x.val := by
    intro X x
    rw [lap_component X (fun z => F z - l0 z) x, lap_sub_fun, hlapl0, sub_zero]
  -- Kirchhoff's law at a terminal of an admissible exterior component
  have hKIR : ∀ t, t ∈ surgeryTerminals → t ∈ D.supp →
      ExteriorAdmissible (comp t) (fun x => F x.val - l0 x.val) →
      lap (openGraph (closedRegion ω)) F t =
        ∑ s ∈ surgeryTerminals, cX (comp t) t s * ((F s - F t) - (l0 s - l0 t)) := by
    intro t htT htD hadm
    have hoff : ∀ x : comp t, x.val ∉ surgeryTerminals →
        lap (componentGraph (comp t)) (fun x => F x.val - l0 x.val) x = 0 := by
      intro x hxT
      rw [hlapfX]
      have hxt : comp x.val = comp t := hcomp_of_mem (X := comp t) x.2
      have hxU : x.val ∉ surgerySites := fun hxU => by
        have := eq_of_reachable_closedRegion hxU (hreach _ _ hxt)
        rw [this] at hxT
        exact hxT htT
      exact hharmX x.val (hsubD t htD x.2) hxU hxT
    have hk := (hcX (comp t)).2.2.2.2 _ hadm hoff ⟨t, hmem t⟩ htT
    calc lap (openGraph (closedRegion ω)) F t
        = lap (componentGraph (comp t)) (fun x => F x.val - l0 x.val) ⟨t, hmem t⟩ :=
          (hlapfX (comp t) ⟨t, hmem t⟩).symm
      _ = ∑ s ∈ surgeryTerminals, cX (comp t) t s *
            (Rigidity.Section3.extend (comp t) (fun x => F x.val - l0 x.val) s -
              (F t - l0 t)) := hk
      _ = ∑ s ∈ surgeryTerminals, cX (comp t) t s * ((F s - F t) - (l0 s - l0 t)) := by
          refine Finset.sum_congr rfl fun s _ => ?_
          by_cases hs : s ∈ (comp t).supp
          · rw [extend_of_mem _ hs]; ring
          · have h0 : cX (comp t) t s = 0 := by
              by_contra h0; exact hs ((hcX (comp t)).2.2.2.1 t s h0).2
            rw [h0, zero_mul, zero_mul]
  -- the infinite exterior component is admissible: slope zero and zero total flux
  have hadmK : ExteriorAdmissible K (fun x => F x.val - l0 x.val) := by
    intro _
    refine ⟨?_, ?_⟩
    · have h1 := componentSlopeAsymptotics_restrict K D hKD hu'.2
      have h2 := componentSlopeAsymptotics_sub K h1 hℓ0.2
      have e : (fun x : K => F x.val - l0 x.val) = fun x => u' ⟨x.val, hKD x.2⟩ - ℓ0 x := by
        funext x
        rw [hFv _ (hKD x.2), hl0K _ x.2]
      rw [e]
      simpa using h2
    · have hJ : ∀ t' ∈ surgeryTerminals, lap (openGraph (closedRegion ω)) F t' =
          ∑ y ∈ ((openGraph ω').neighborFinset t').filter (· ∉ surgerySites), (F y - F t') :=
        fun t' ht' => hext t' (not_mem_surgerySites_of_mem_terminals ht')
      have e1 : ∑ t' ∈ surgeryTerminals.subtype (· ∈ K),
          lap (componentGraph K) (fun x => F x.val - l0 x.val) t' =
          ∑ t' ∈ surgeryTerminals.filter (· ∈ K), lap (openGraph (closedRegion ω)) F t' := by
        rw [← Finset.sum_subtype_eq_sum_filter]
        exact Finset.sum_congr rfl fun x _ => hlapfX K x
      rw [e1]
      have h0 := sum_exterior_current_eq_zero D F hFharm
      rw [← Finset.sum_filter_add_sum_filter_not _ (· ∈ K), Finset.filter_filter,
        Finset.filter_filter] at h0
      have hfK : surgeryTerminals.filter (fun a => a ∈ D.supp ∧ a ∈ K) =
          surgeryTerminals.filter (· ∈ K) :=
        Finset.filter_congr fun a _ => ⟨fun h => h.2, fun h => ⟨hKD h, h⟩⟩
      rw [hfK] at h0
      set Q := surgeryTerminals.filter (fun a => a ∈ D.supp ∧ ¬ a ∈ K) with hQ
      have hQmem : ∀ a, a ∈ Q ↔ a ∈ surgeryTerminals ∧ a ∈ D.supp ∧ a ∉ K := fun a => by
        rw [hQ, Finset.mem_filter]
      have hQ' : ∀ t' ∈ Q, ∀ s ∈ surgeryTerminals, cX (comp t') t' s ≠ 0 → s ∈ Q := by
        intro t' ht' s hs hc
        obtain ⟨-, ht'D, ht'K⟩ := (hQmem t').1 ht'
        have e := hsupp' t' s hc
        refine (hQmem s).2 ⟨hs, hsubD t' ht'D (by rw [← e]; exact hmem s), fun hsK => ht'K ?_⟩
        have hK' : comp t' = K := e.symm.trans (hcomp_of_mem hsK)
        rw [← hK']
        exact hmem t'
      have hsumQ : ∑ t' ∈ Q, ∑ y ∈ ((openGraph ω').neighborFinset t').filter (· ∉ surgerySites),
          (F y - F t') = 0 := by
        have e2 : ∀ t' ∈ Q, ∑ y ∈ ((openGraph ω').neighborFinset t').filter (· ∉ surgerySites),
            (F y - F t') = ∑ s ∈ Q, cX (comp t') t' s * ((F s - F t') - (l0 s - l0 t')) := by
          intro t' ht'
          obtain ⟨ht'T, ht'D, ht'K⟩ := (hQmem t').1 ht'
          have hadm : ExteriorAdmissible (comp t') (fun x => F x.val - l0 x.val) := by
            intro hinf
            exact absurd (by rw [← hKuniq _ hinf]; exact hmem t') ht'K
          rw [← hJ t' ht'T, hKIR t' ht'T ht'D hadm]
          refine (Finset.sum_subset (Finset.filter_subset _ _) fun s hs hsQ => ?_).symm
          have h0' : cX (comp t') t' s = 0 := by
            by_contra h0'; exact hsQ (hQ' t' ht' s hs h0')
          rw [h0', zero_mul]
        rw [Finset.sum_congr rfl e2]
        exact sum_sum_antisymm_eq_zero Q _ fun a b => by rw [← hsymc]; ring
      rw [hsumQ, add_zero] at h0
      rw [← h0]
      exact Finset.sum_congr rfl fun t' ht' => hJ t' (Finset.mem_filter.1 ht').1
  -- Kirchhoff's law at the terminal `t`
  have hadm_t : ExteriorAdmissible (comp t) (fun x => F x.val - l0 x.val) := by
    by_cases hinf : (comp t).supp.Infinite
    · rw [hKuniq _ hinf]; exact hadmK
    · exact fun h => absurd h hinf
  have hk := hKIR t htT htD hadm_t
  have hext_t := hext t (not_mem_surgerySites_of_mem_terminals htT)
  have hharm_t := hFharm t htD
  rw [lap, ← Finset.sum_filter_add_sum_filter_not _ (· ∈ surgerySites)] at hharm_t
  have e1 : ∑ y ∈ ((componentGraph D).neighborFinset ⟨t, htD⟩).filter
      (fun y => y.val ∈ surgerySites), (u' y - u' ⟨t, htD⟩) =
      ∑ y ∈ ((openGraph ω').neighborFinset t).filter (· ∈ surgerySites), (F y - F t) := by
    rw [← sum_component_neighbor_filter D ⟨t, htD⟩ (· ∈ surgerySites) (fun y => F y - F t)]
    refine Finset.sum_congr rfl fun y _ => ?_
    show u' y - u' ⟨t, htD⟩ = F y.val - F t
    rw [hFv y.val y.2, hFv t htD]
  rw [e1]
  linarith

/-! ### The closed environment is typical -/

/-- Almost surely the environment has the typical properties used for the exterior network: the
uniqueness of the infinite cluster, a corrected plane, the Liouville property (Armstrong–Dario at
order zero) and Green columns with the asymptotics of Dario and Gu (with `δ = 1/4`). -/
theorem ae_exteriorTypical (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hcor : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hAD : LatticeProb.External.ArmstrongDarioOrderZero)
    (hGE : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative) {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∀ᵐ η ∂latticeBondLaw 2 p, ExteriorTypical η := by
  obtain ⟨κ, hκ, hQ2, -⟩ := hGQ 2 le_rfl p hpc hp1
  obtain ⟨Kf, -, hQ⟩ := hQ2 rfl
  obtain ⟨C, s, -, -, hQy⟩ := hQ (1 / 4) (by norm_num)
  choose M hM using fun y => (hQy y).2
  have hQae := ae_all_iff.2 fun y => (hM y).2.2.2
  have hEae := ae_all_iff.2 fun y => hGE 2 le_rfl p hpc hp1 y
  have hUae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ uniqueInfiniteComponentEvent 2 :=
    (ae_iff_measure_eq (measurableSet_uniqueInfiniteComponentEvent 2).nullMeasurableSet).2
      (by rw [measure_univ]; exact hUq.2 2 le_rfl p hpc hp1)
  have hLae := sublinearLiouvilleStep (d := 2) le_rfl p hpc hp1 hAD
  filter_upwards [hUae, hcor 2 le_rfl p hpc hp1, hLae, hQae, hEae] with η hU hc hL hQη hEη
  refine ⟨hU, ?_, hL hU, κ, hκ, fun r _ => ?_⟩
  · obtain ⟨v, hv⟩ := (uniqueInfiniteComponent hU).nonempty_supp
    obtain ⟨u, hu, -⟩ := ((hc hU).1 (Pi.single 0 1) ⟨v, hv⟩).exists
    exact ⟨u, hu⟩
  · obtain ⟨g, hg⟩ := (hEη r.val hU r.2).exists
    refine ⟨g, Kf r.val η, M r.val η, C, hg, fun x hxr hxM => ?_⟩
    have hne : latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding r.val ≠ 0 := by
      rw [sub_ne_zero]
      exact fun h => hxr (Subtype.ext (latticeEuclideanEmbedding.injective h))
    have hb := (hQη r.val hU r.2 g hg).2 x ⟨_, hne⟩ rfl hxM
    have hG : continuumGreen 2 le_rfl ⟨κ, hκ⟩ ⟨_, hne⟩ =
        -Real.log ‖latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding r.val‖ /
          (2 * Real.pi * κ) := by
      simp [continuumGreen]
    have hpow : Real.rpow ‖latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding r.val‖
        (1 - 1 / 4) =
        ‖latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding r.val‖ ^ (3 / 4 : ℝ) := by
      rw [Real.rpow_eq_pow]; norm_num
    rw [hG, hpow] at hb
    have e : g x + Real.log ‖latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding r.val‖ /
          (2 * Real.pi * κ) - Kf r.val η =
        g x - -Real.log ‖latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding r.val‖ /
          (2 * Real.pi * κ) - Kf r.val η := by ring
    rw [e]
    exact hb

/-- **The exterior network of the surgery region** (`ExteriorNetworkStep p`, the new ingredient
of the signed variant of Proposition 3.2), for `p_c(2) < p < 1`, from the literature inputs on the
uniqueness of the infinite cluster, the corrected planes, the Liouville property at order zero and
the Green function of the infinite cluster (existence and the asymptotics of Dario and Gu): by
finite energy the environment with the bonds of the region closed is typical
(`ae_exteriorTypical`, `modifyNear_preimage_null`), and its exterior components give the network
(`exteriorNetworkAt_of_typical`). With `horizontalIncrementStep_of_exteriorNetwork_inputs` this
gives the signed variant `HorizontalIncrementStep p`, the directional step of the printed
Lemma 5.25, from the literature inputs. -/
theorem exteriorNetworkStep (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hcor : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hAD : LatticeProb.External.ArmstrongDarioOrderZero)
    (hGE : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative) {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) : ExteriorNetworkStep p := by
  have hp0 : 0 < (p : ℝ) := lt_trans (hUq.1 2 le_rfl).1 hpc
  have hnull : latticeBondLaw 2 p {η | ¬ ExteriorTypical η} = 0 :=
    ae_iff.1 (ae_exteriorTypical hUq hcor hAD hGE hGQ hpc hp1)
  have h2 := modifyNear_preimage_null hp0 hp1 meetsSites_surgerySites_bondsNear ∅ hnull
  have h3 : ∀ᵐ ω ∂latticeBondLaw 2 p, ExteriorTypical (closedRegion ω) := ae_iff.2 h2
  filter_upwards [h3] with ω hω
  exact exteriorNetworkAt_of_typical hω

end Rigidity.Proofs.S3
