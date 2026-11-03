import Rigidity.Proofs.S4.OuterNonConstant.Compare
import Rigidity.Proofs.S4.OuterNonConstant.Reset
import Rigidity.Proofs.S4.OuterNonConstant.Geometry

/-!
# Lemma 4.8, conditional form: the comparison and attachment environments

Deterministic facts on `compareEnv d R ω` (`ρ₀`) and `attachEnv hd R w ω` (`ω^♮_w`).
-/

namespace Rigidity.Proofs.S4.OuterNonConstant

open LatticeProb LatticeProb.Percolation LatticeProb.Network
  LatticeProb.Network.OpenLadder.Embedding Rigidity.Section4 Rigidity.Steps.S4

open scoped Classical

variable {d : ℕ} {R : ℕ} {ω : Configuration d} {w : Vertex d}

/-- A site of a bond is adjacent to the other site of the bond. -/
theorem exists_adj_of_mem {e : Bond d} {z : Vertex d} (hz : z ∈ (e : Sym2 (Vertex d))) :
    ∃ y, (nearestNeighborGraph d).Adj z y ∧ (e : Sym2 (Vertex d)) = s(z, y) := by
  obtain ⟨a, b, hab, h1⟩ := e.2
  rw [hab, Sym2.mem_iff] at hz
  rcases hz with rfl | rfl
  · exact ⟨b, lattice_adj_iff_l1Dist.mpr h1, hab⟩
  · exact ⟨a, (lattice_adj_iff_l1Dist.mpr h1).symm, hab.trans Sym2.eq_swap⟩

/-- A bond at a site of `Q_{R-1}` has no skeleton endpoint. -/
theorem mem_coreBonds_of_mem_cube_pred (hR : 1 ≤ R) {e : Bond d} {z : Vertex d}
    (hz : z ∈ (e : Sym2 (Vertex d))) (hzc : z ∈ cube d (R - 1)) : e ∈ coreBonds d R := by
  obtain ⟨y, hzy, he⟩ := exists_adj_of_mem hz
  intro u hu
  rw [he, Sym2.mem_iff] at hu
  rcases hu with rfl | rfl
  · exact Or.inr hzc
  · exact (mem_cube_pred_or_faceSites_of_adj hR hzc hzy).symm

theorem not_mem_faceSites_of_mem_cube_pred (hR : 1 ≤ R) {z : Vertex d} (hz : z ∈ cube d (R - 1)) :
    z ∉ faceSites d R := fun h => not_mem_cube_pred_of_mem_faceSites hR h hz

/-- A component of a graph in which `z` has no neighbour is `{z}`. -/
theorem supp_subset_singleton {V : Type*} {G : SimpleGraph V} {C : G.ConnectedComponent} {z : V}
    (hz : z ∈ C.supp) (h : ∀ y, ¬ G.Adj z y) : C.supp ⊆ {z} := by
  intro y hy
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hz hy
  obtain ⟨W⟩ := SimpleGraph.ConnectedComponent.exact (hz.trans hy.symm)
  cases W with
  | nil => rfl
  | cons hadj _ => exact absurd hadj (h _)

/-! ### The comparison environment `ρ₀` -/

theorem compareEnv_apply (e : Bond d) : compareEnv d R ω e =
    if e ∈ coreBonds d R ∪ connectorBonds d R then
      decide (e ∈ faceBonds d R ∨ e ∈ connectorBonds d R) else ω e := by
  unfold compareEnv
  by_cases he : e ∈ coreBonds d R ∪ connectorBonds d R
  · rw [resetConfig_of_mem he, if_pos he]
  · rw [resetConfig_of_not_mem he, if_neg he]

/-- The sites of `Q_{R-1}` are isolated in `ρ₀`. -/
theorem compareEnv_not_adj (hR : 2 ≤ R) {z y : Vertex d} (hz : z ∈ cube d (R - 1)) :
    ¬ (openGraph (compareEnv d R ω)).Adj z y := by
  rintro ⟨hzy, hopen⟩
  have hzb : z ∈ ((bondOfAdjacent hzy : Bond d) : Sym2 (Vertex d)) := Sym2.mem_mk_left z y
  have hcore := mem_coreBonds_of_mem_cube_pred (by omega) hzb hz
  rw [compareEnv_apply, if_pos (Set.mem_union_left _ hcore), decide_eq_true_eq] at hopen
  rcases hopen with hf | hk
  · exact not_mem_faceSites_of_mem_cube_pred (by omega) hz (hf z hzb)
  · exact not_mem_cube_pred_of_mem_connectorBonds hR hk z hzb hz

/-- No site of `Q_{R-1}` lies in an infinite cluster of `ρ₀`. -/
theorem not_mem_supp_compareEnv (hR : 2 ≤ R) (C : OpenComponent (compareEnv d R ω))
    (hC : C.supp.Infinite) {z : Vertex d} (hz : z ∈ cube d (R - 1)) : z ∉ C.supp := fun hzC =>
  hC ((Set.finite_singleton z).subset
    (supp_subset_singleton hzC fun _ => compareEnv_not_adj (ω := ω) hR hz))

/-! ### The attachment environment `ω^♮_w` -/

theorem attachEnv_apply (hd : 2 ≤ d) (e : Bond d) : attachEnv hd R w ω e =
    if e ∈ attachResetBonds hd R w then
      decide (e ∈ faceBonds d R ∨ e ∈ connectorBonds d R ∨ e ∈ branchBonds hd R w)
    else ω e := by
  unfold attachEnv
  by_cases he : e ∈ attachResetBonds hd R w
  · rw [resetConfig_of_mem he, if_pos he]; rfl
  · rw [resetConfig_of_not_mem he, if_neg he]

theorem attachResetBonds_subset (hd : 2 ≤ d) :
    attachResetBonds hd R w ⊆ coreBonds d R ∪ connectorBonds d R := by
  rintro e (⟨hc, -⟩ | hk)
  · exact Or.inl hc
  · exact Or.inr hk

theorem faceBonds_subset_coreBonds : faceBonds d R ⊆ coreBonds d R :=
  fun _ he z hz => Or.inl (he z hz)

theorem mem_attachResetBonds_of_faceBonds (hd : 2 ≤ d) {e : Bond d}
    (he : e ∈ faceBonds d R) : e ∈ attachResetBonds hd R w := by
  obtain ⟨a, b, hab, -⟩ := e.2
  have ha : a ∈ (e : Sym2 (Vertex d)) := by rw [hab]; exact Sym2.mem_mk_left a b
  exact Or.inl ⟨faceBonds_subset_coreBonds he, a, ha, Or.inl (he a ha)⟩

/-- `ρ₀ ≤ ω^♮_w`. -/
theorem compareEnv_le_attachEnv (hd : 2 ≤ d) {e : Bond d}
    (he : compareEnv d R ω e = true) : attachEnv hd R w ω e = true := by
  rw [compareEnv_apply] at he
  split_ifs at he with hD
  · rw [decide_eq_true_eq] at he
    rw [attachEnv_apply hd]
    rcases he with hf | hk
    · rw [if_pos (mem_attachResetBonds_of_faceBonds hd hf), decide_eq_true_eq]
      exact Or.inl hf
    · have hk' : e ∈ attachResetBonds hd R w := Set.mem_union_right _ hk
      rw [if_pos hk', decide_eq_true_eq]
      exact Or.inr (Or.inl hk)
  · rw [attachEnv_apply hd, if_neg fun h => hD (attachResetBonds_subset hd h)]
    exact he

theorem openGraph_compareEnv_le (hd : 2 ≤ d) {z y : Vertex d}
    (h : (openGraph (compareEnv d R ω)).Adj z y) :
    (openGraph (attachEnv hd R w ω)).Adj z y :=
  ⟨h.1, compareEnv_le_attachEnv hd h.2⟩

/-! ### The branch -/

theorem refSite_mem (hd : 2 ≤ d) (hR : 10 ≤ R) : refSite d R ∈ faceSites d R :=
  refSite_mem_faceSites hd (by omega)

section Branch

variable (hd : 2 ≤ d) (hR : 10 ≤ R) (hw : w ∈ faceSites d R) (hw0 : w ≠ refSite d R)
include hd hR hw hw0

omit hw hw0 in
theorem gadget_site_mem_cube_pred {z : Vertex d} (hz : z - gadgetShift d R ∈ ambientSites hd (R : ℤ)) :
    z ∈ cube d (R - 1) := by
  have := gadget_mem_cube_pred hd hR hz
  rwa [add_sub_cancel] at this

/-- The branch bonds have no skeleton endpoint. -/
theorem branchBonds_core {e : Bond d} (he : e ∈ branchBonds hd R w) : e ∈ coreBonds d R := by
  intro z hz
  rcases he with ((hg | hl) | hh) | ha
  · exact Or.inr (gadget_site_mem_cube_pred hd hR (hg z hz))
  · exact Or.inr (lowBranch_sites hd hR hw hw0 z ⟨e, hl, hz⟩).1
  · exact Or.inr (highBranch_sites hd hR z ⟨e, hh, hz⟩).1
  · rcases ha with ha | ha <;> rw [ha, Sym2.mem_iff] at hz
    · rcases hz with rfl | rfl
      · exact Or.inl hw
      · exact Or.inr (innerNeighbor_mem_cube (by omega) hw)
    · rcases hz with rfl | rfl
      · exact Or.inl (refSite_mem hd hR)
      · exact Or.inr (innerNeighbor_mem_cube (by omega) (refSite_mem hd hR))

theorem mem_attachResetBonds_of_branch {e : Bond d} (he : e ∈ branchBonds hd R w) :
    e ∈ attachResetBonds hd R w := by
  obtain ⟨a, b, hab, -⟩ := e.2
  have ha : a ∈ (e : Sym2 (Vertex d)) := by rw [hab]; exact Sym2.mem_mk_left a b
  exact Or.inl ⟨branchBonds_core hd hR hw hw0 he, a, ha, Or.inr ⟨e, he, ha⟩⟩

theorem attachEnv_branch {e : Bond d} (he : e ∈ branchBonds hd R w) :
    attachEnv hd R w ω e = true := by
  rw [attachEnv_apply hd, if_pos (mem_attachResetBonds_of_branch hd hR hw hw0 he),
    decide_eq_true_eq]
  exact Or.inr (Or.inr he)

/-- The open bonds of `ω^♮_w` that are closed in `ρ₀`, at a site outside `Q_{R-1}`: the two
attachment bonds. -/
theorem attachEnv_extra {z y : Vertex d} (h1 : (openGraph (attachEnv hd R w ω)).Adj z y)
    (h2 : ¬ (openGraph (compareEnv d R ω)).Adj z y) (hz : z ∉ cube d (R - 1)) :
    (z = w ∧ y = innerNeighbor R w) ∨
      (z = refSite d R ∧ y = innerNeighbor R (refSite d R)) := by
  obtain ⟨hzy, hopen⟩ := h1
  have hc : compareEnv d R ω (bondOfAdjacent hzy) = false := by
    by_contra hc
    exact h2 ⟨hzy, by simpa using hc⟩
  have hzb : z ∈ ((bondOfAdjacent hzy : Bond d) : Sym2 (Vertex d)) := Sym2.mem_mk_left z y
  rw [attachEnv_apply hd] at hopen
  split_ifs at hopen with hb
  · rw [decide_eq_true_eq] at hopen
    rcases hopen with hf | hk | hbr
    · rw [compareEnv_apply, if_pos (Set.mem_union_left _ (faceBonds_subset_coreBonds hf))] at hc
      simp [hf] at hc
    · rw [compareEnv_apply, if_pos (Set.mem_union_right _ hk)] at hc
      simp [hk] at hc
    · rcases hbr with ((hg | hl) | hh) | ha
      · exact absurd (gadget_site_mem_cube_pred hd hR (hg z hzb)) hz
      · exact absurd (lowBranch_sites hd hR hw hw0 z ⟨_, hl, hzb⟩).1 hz
      · exact absurd (highBranch_sites hd hR z ⟨_, hh, hzb⟩).1 hz
      · have hR1 : 1 ≤ R := by omega
        rcases ha with ha | ha <;> change s(z, y) = _ at ha <;>
          rcases Sym2.eq_iff.mp ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl ⟨rfl, rfl⟩
        · exact absurd (innerNeighbor_mem_cube hR1 hw) hz
        · exact Or.inr ⟨rfl, rfl⟩
        · exact absurd (innerNeighbor_mem_cube hR1 (refSite_mem hd hR)) hz
  · rw [compareEnv_apply] at hc
    split_ifs at hc with hD
    · rcases hD with hcore | hk
      · rcases hcore z hzb with hzf | hzc
        · exact absurd (Or.inl ⟨hcore, z, hzb, Or.inl hzf⟩) hb
        · exact absurd hzc hz
      · exact absurd (Or.inr hk) hb
    · rw [hc] at hopen
      exact absurd hopen (by simp)

end Branch

/-- If `ω₁ ≤ ω₂`, the unique infinite cluster of `ω₁` lies in that of `ω₂`. -/
theorem supp_subset_of_adj_le {ω₁ ω₂ : Configuration d}
    (hle : ∀ z y, (openGraph ω₁).Adj z y → (openGraph ω₂).Adj z y)
    (h₁ : HasUniqueInfiniteOpenComponent ω₁) (h₂ : HasUniqueInfiniteOpenComponent ω₂) :
    (uniqueInfiniteComponent h₁).supp ⊆ (uniqueInfiniteComponent h₂).supp := by
  obtain ⟨o, ho⟩ := (uniqueInfiniteComponent_infinite h₁).nonempty
  have hsub : (uniqueInfiniteComponent h₁).supp ⊆
      ((openGraph ω₂).connectedComponentMk o).supp := by
    intro z hz
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hz ho ⊢
    exact SimpleGraph.ConnectedComponent.sound
      (SimpleGraph.Reachable.mono (fun a b h => hle a b h)
        (SimpleGraph.ConnectedComponent.exact (hz.trans ho.symm)))
  have hinf : ((openGraph ω₂).connectedComponentMk o).supp.Infinite :=
    Set.Infinite.mono hsub (uniqueInfiniteComponent_infinite h₁)
  rwa [(eq_uniqueInfiniteComponent_iff h₂ _).mpr hinf] at hsub

/-- The gadget sites are joined by open gadget bonds. -/
theorem gadget_reachable_of_open (hd : 2 ≤ d) (hR : 4 ≤ R) {ω' : Configuration d}
    (hopen : ∀ e ∈ gadgetBonds hd R, ω' e = true) {g g' : Vertex d}
    (hg : g ∈ ambientSites hd (R : ℤ)) (hg' : g' ∈ ambientSites hd (R : ℤ)) :
    (openGraph ω').Reachable (gadgetShift d R + g) (gadgetShift d R + g') := by
  let φ : ambientGraph hd (R : ℤ) →g openGraph ω' :=
    { toFun := fun g => gadgetShift d R + g.val
      map_rel' := fun {a b} hab => by
        have hadj : (nearestNeighborGraph d).Adj (gadgetShift d R + a.val)
            (gadgetShift d R + b.val) := by
          rw [add_comm (gadgetShift d R) a.val, add_comm (gadgetShift d R) b.val,
            nearestNeighborGraph_adj_add_iff]
          exact hab
        refine ⟨hadj, hopen _ ?_⟩
        intro z hz
        simp only [bondOfAdjacent, Sym2.mem_iff] at hz
        rcases hz with rfl | rfl
        · simp
        · simp }
  have hconn : (ambientGraph hd (R : ℤ)).Connected :=
    (ambientIso hd (R : ℤ)).connected_iff.mp (OpenLadder.connected (by omega))
  exact (hconn.preconnected ⟨g, hg⟩ ⟨g', hg'⟩).map φ

/-- Reachability preserves membership in a component. -/
theorem mem_supp_of_reachable {ω' : Configuration d} (K : OpenComponent ω') {a b : Vertex d}
    (ha : a ∈ K.supp) (hab : (openGraph ω').Reachable a b) : b ∈ K.supp := by
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at ha ⊢
  rw [← ha]
  exact (SimpleGraph.ConnectedComponent.sound hab).symm

/-- **The Liouville argument** (paper L1415) for the attachment at `w` and `z₀`. Let `ρ₀` have a
unique infinite cluster `𝒞₀ ⊇` face sites, on which sublinear harmonic functions are constant, and a
corrected plane `ℓ₀` with `ℓ₀(w) ≠ ℓ₀(z₀)`. Then every corrected plane of the cluster of `ω^♮_w`
is not constant on the gadget: otherwise it is constant along `P₁` and `P₂`, the attachment bonds
carry no current, its restriction to `𝒞₀` is harmonic for `ρ₀`, and it differs from `ℓ₀` by a
constant. -/
theorem attach_gadget_nonconstant (hd : 2 ≤ d) (hR : 10 ≤ R) (hw : w ∈ faceSites d R)
    (hw0 : w ≠ refSite d R) {q : Fin d → ℝ}
    (C : OpenComponent (compareEnv d R ω)) (hCinf : C.supp.Infinite)
    (hface : faceSites d R ⊆ C.supp) (ℓ₀ : C → ℝ) (hℓ₀ : IsCorrectedPlane C q ℓ₀)
    (hne : ℓ₀ ⟨w, hface hw⟩ ≠ ℓ₀ ⟨refSite d R, hface (refSite_mem hd hR)⟩)
    (hliou : ∀ v : C → ℝ, (∀ z, componentLaplacian C v z = 0) →
      componentSlopeAsymptotics C 0 v → ∃ c : ℝ, ∀ z, v z = c)
    (K : OpenComponent (attachEnv hd R w ω)) (hCK : C.supp ⊆ K.supp)
    (u : K → ℝ) (hu : IsCorrectedPlane K q u) :
    ∃ g ∈ ambientSites hd (R : ℤ), ∃ g' ∈ ambientSites hd (R : ℤ),
      ∃ hg : gadgetShift d R + g ∈ K.supp, ∃ hg' : gadgetShift d R + g' ∈ K.supp,
        u ⟨gadgetShift d R + g, hg⟩ ≠ u ⟨gadgetShift d R + g', hg'⟩ := by
  have hR1 : 1 ≤ R := by omega
  have hz₀ := refSite_mem hd hR
  have hwK : w ∈ K.supp := hCK (hface hw)
  have hz₀K : refSite d R ∈ K.supp := hCK (hface hz₀)
  have hw1 : (openGraph (attachEnv hd R w ω)).Adj (innerNeighbor R w) w := by
    refine ⟨(adj_innerNeighbor hR1 hw).symm, attachEnv_branch hd hR hw hw0 (Or.inr (Or.inl ?_))⟩
    exact Sym2.eq_swap
  have hz1 : (openGraph (attachEnv hd R w ω)).Adj (zeroPad d (1, -((R : ℤ) - 1))) (refSite d R) := by
    rw [← innerNeighbor_refSite (by omega)]
    refine ⟨(adj_innerNeighbor hR1 hz₀).symm,
      attachEnv_branch hd hR hw hw0 (Or.inr (Or.inr ?_))⟩
    exact Sym2.eq_swap
  have hlowopen : ∀ f ∈ chainBonds (lowWaypoints hd R w), (attachEnv hd R w ω) f = true :=
    fun f hf => attachEnv_branch hd hR hw hw0 (Or.inl (Or.inl (Or.inr hf)))
  have hhighopen : ∀ f ∈ chainBonds (highWaypoints d R), (attachEnv hd R w ω) f = true :=
    fun f hf => attachEnv_branch hd hR hw hw0 (Or.inl (Or.inr hf))
  have hgadopen : ∀ f ∈ gadgetBonds hd R, (attachEnv hd R w ω) f = true :=
    fun f hf => attachEnv_branch hd hR hw hw0 (Or.inl (Or.inl (Or.inl hf)))
  have hlowreach : ∀ z ∈ bondSites (chainBonds (lowWaypoints hd R w)),
      ∃ W : (nearestNeighborGraph d).Walk (innerNeighbor R w) z,
        ∀ e ∈ W.edges, ∃ f ∈ chainBonds (lowWaypoints hd R w), (f : Sym2 (Vertex d)) = e :=
    fun z hz => chainBonds_reach (innerNeighbor R w) (lowWaypoints hd R w).tail z hz
  have hhighreach : ∀ z ∈ bondSites (chainBonds (highWaypoints d R)),
      ∃ W : (nearestNeighborGraph d).Walk (zeroPad d (1, -((R : ℤ) - 1))) z,
        ∀ e ∈ W.edges, ∃ f ∈ chainBonds (highWaypoints d R), (f : Sym2 (Vertex d)) = e :=
    fun z hz => chainBonds_reach _ _ z hz
  have hw1K : innerNeighbor R w ∈ K.supp := mem_supp_of_reachable K hwK hw1.symm.reachable
  have hlowK : ∀ z ∈ bondSites (chainBonds (lowWaypoints hd R w)), z ∈ K.supp := by
    intro z hz
    obtain ⟨W, hW⟩ := hlowreach z hz
    exact mem_supp_of_reachable K hw1K (openGraph_reachable_of_walk hlowopen W hW)
  have hz1K : zeroPad d (1, -((R : ℤ) - 1)) ∈ K.supp :=
    mem_supp_of_reachable K hz₀K hz1.symm.reachable
  have hhighK : ∀ z ∈ bondSites (chainBonds (highWaypoints d R)), z ∈ K.supp := by
    intro z hz
    obtain ⟨W, hW⟩ := hhighreach z hz
    exact mem_supp_of_reachable K hz1K (openGraph_reachable_of_walk hhighopen W hW)
  have hsK := hlowK _ (lowBranch_ends hd hR hw).2
  have hgK : ∀ g ∈ ambientSites hd (R : ℤ), gadgetShift d R + g ∈ K.supp := by
    intro g hg
    have h := gadget_reachable_of_open hd (by omega) hgadopen (zeroPad_s_mem hd R) hg
    rw [add_sub_cancel] at h
    exact mem_supp_of_reachable K hsK h
  by_contra hcon
  push Not at hcon
  set U : Vertex d → ℝ := Rigidity.Section3.extend K u with hU
  have hUK : ∀ z (hz : z ∈ K.supp), U z = u ⟨z, hz⟩ := fun z hz => by
    simp [hU, Rigidity.Section3.extend, hz]
  have hharm : ∀ z ∈ K.supp, Graph.laplacian (openGraph (attachEnv hd R w ω)) U z = 0 := by
    intro z hz
    rw [← componentLaplacian_restrict_eq K U ⟨z, hz⟩]
    have : (fun y : K => U y.val) = u := funext fun y => hUK y.val y.2
    rw [this]
    exact hu.1.1 ⟨z, hz⟩
  have hgad : ∀ z z', z - gadgetShift d R ∈ ambientSites hd (R : ℤ) →
      z' - gadgetShift d R ∈ ambientSites hd (R : ℤ) → U z = U z' := by
    intro z z' hz hz'
    calc U z = U (gadgetShift d R + (z - gadgetShift d R)) := by rw [add_sub_cancel]
      _ = u ⟨_, hgK _ hz⟩ := hUK _ _
      _ = u ⟨_, hgK _ hz'⟩ := hcon _ hz _ hz' _ _
      _ = U (gadgetShift d R + (z' - gadgetShift d R)) := (hUK _ _).symm
      _ = U z' := by rw [add_sub_cancel]
  have hbr : ∀ {z : Vertex d} {B : Set (Bond d)}, B ⊆ branchBonds hd R w → z ∈ bondSites B →
      z ∈ bondSites (branchBonds hd R w) := fun hB ⟨e, he, hze⟩ => ⟨e, hB he, hze⟩
  -- the open neighbours of the sites of `P₁` and `P₂`
  have hout : ∀ z ∈ cube d (R - 1), z ∈ bondSites (branchBonds hd R w) → ∀ y,
      (openGraph (attachEnv hd R w ω)).Adj z y →
        (z - gadgetShift d R ∈ ambientSites hd (R : ℤ) ∧
            y - gadgetShift d R ∈ ambientSites hd (R : ℤ)) ∨
          (z ∈ bondSites (chainBonds (lowWaypoints hd R w)) ∧
            y ∈ bondSites (chainBonds (lowWaypoints hd R w))) ∨
          (z ∈ bondSites (chainBonds (highWaypoints d R)) ∧
            y ∈ bondSites (chainBonds (highWaypoints d R))) ∨
          (z = innerNeighbor R w ∧ y = w) ∨
          (z = innerNeighbor R (refSite d R) ∧ y = refSite d R) := by
    intro z hzc hzbr y ⟨hadj, hopen⟩
    have hzb : z ∈ ((bondOfAdjacent hadj : Bond d) : Sym2 (Vertex d)) := Sym2.mem_mk_left z y
    have hyb : y ∈ ((bondOfAdjacent hadj : Bond d) : Sym2 (Vertex d)) := Sym2.mem_mk_right z y
    have hD : bondOfAdjacent hadj ∈ attachResetBonds hd R w :=
      Or.inl ⟨mem_coreBonds_of_mem_cube_pred hR1 hzb hzc, z, hzb, Or.inr hzbr⟩
    rw [attachEnv_apply hd, if_pos hD, decide_eq_true_eq] at hopen
    rcases hopen with hf | hk | hb
    · exact absurd (hf z hzb) (not_mem_faceSites_of_mem_cube_pred hR1 hzc)
    · exact absurd hzc (not_mem_cube_pred_of_mem_connectorBonds (by omega) hk z hzb)
    rcases hb with ((hg | hl) | hh) | ha
    · exact Or.inl ⟨hg z hzb, hg y hyb⟩
    · exact Or.inr (Or.inl ⟨⟨_, hl, hzb⟩, ⟨_, hl, hyb⟩⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨⟨_, hh, hzb⟩, ⟨_, hh, hyb⟩⟩))
    · rcases ha with ha | ha <;> change s(z, y) = _ at ha <;>
        rcases Sym2.eq_iff.mp ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd hw (not_mem_faceSites_of_mem_cube_pred hR1 hzc)
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
      · exact absurd hz₀ (not_mem_faceSites_of_mem_cube_pred hR1 hzc)
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
  have hz1h : innerNeighbor R (refSite d R) ∈ bondSites (chainBonds (highWaypoints d R)) := by
    rw [innerNeighbor_refSite (by omega)]; exact (highBranch_ends hd hR).1
  have hPlow := path_value_eq (ω' := attachEnv hd R w ω) (U := U) (P := chainBonds (lowWaypoints hd R w))
    ((cube_finite d (R - 1)).subset fun z hz => (lowBranch_sites hd hR hw hw0 z hz).1) hw1
    hlowreach hlowopen (fun z hz => hharm z (hlowK z hz)) (by
      intro z hz y hzy
      obtain ⟨hzc, hzh, -⟩ := lowBranch_sites hd hR hw hw0 z hz
      rcases hout z hzc (hbr (fun e he => Or.inl (Or.inl (Or.inr he))) hz) y hzy with
        ⟨hg, hg'⟩ | ⟨-, hy⟩ | ⟨hzh', -⟩ | ⟨-, rfl⟩ | ⟨rfl, -⟩
      · exact Or.inr (Or.inr (hgad y z hg' hg))
      · exact Or.inl hy
      · exact absurd hzh' hzh
      · exact Or.inr (Or.inl rfl)
      · exact absurd hz1h hzh)
  have hPhigh := path_value_eq (ω' := attachEnv hd R w ω) (U := U) (P := chainBonds (highWaypoints d R))
    ((cube_finite d (R - 1)).subset fun z hz => (highBranch_sites hd hR z hz).1) hz1
    hhighreach hhighopen (fun z hz => hharm z (hhighK z hz)) (by
      intro z hz y hzy
      have hzc := (highBranch_sites hd hR z hz).1
      have hzl : z ∉ bondSites (chainBonds (lowWaypoints hd R w)) :=
        fun h => (lowBranch_sites hd hR hw hw0 z h).2.1 hz
      rcases hout z hzc (hbr (fun e he => Or.inl (Or.inr he)) hz) y hzy with
        ⟨hg, hg'⟩ | ⟨hzl', -⟩ | ⟨-, hy⟩ | ⟨rfl, -⟩ | ⟨-, rfl⟩
      · exact Or.inr (Or.inr (hgad y z hg' hg))
      · exact absurd hzl' hzl
      · exact Or.inl hy
      · exact absurd (lowBranch_ends hd hR hw).1 hzl
      · exact Or.inr (Or.inl rfl))
  have e1 := hPlow _ (lowBranch_ends hd hR hw).2
  have e2 := hPhigh _ (highBranch_ends hd hR).2
  have e3 := hgad _ _ (zeroPad_s_mem hd R) (zeroPad_t_mem hd R)
  have ew1 := hPlow _ (lowBranch_ends hd hR hw).1
  have ez1 : U (innerNeighbor R (refSite d R)) = U (refSite d R) := hPhigh _ hz1h
  -- `U` is harmonic on `𝒞₀` for `ρ₀`
  have hlapC : ∀ z ∈ C.supp, Graph.laplacian (openGraph (compareEnv d R ω)) U z = 0 := by
    intro z hz
    have hzc : z ∉ cube d (R - 1) := fun h =>
      not_mem_supp_compareEnv (by omega) C hCinf h hz
    rw [laplacian_eq_of_adj (ω₂ := (attachEnv hd R w ω)) U z (fun y hy => openGraph_compareEnv_le hd hy)]
    · exact hharm z (hCK hz)
    intro y hy hny
    rcases attachEnv_extra hd hR hw hw0 hy hny hzc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ew1
    · exact ez1
  -- `U - ℓ₀` is a sublinear harmonic function on `𝒞₀`
  set v : C → ℝ := fun z => U z.val - ℓ₀ z with hv
  have hvlap : ∀ z, componentLaplacian C v z = 0 := by
    intro z
    calc componentLaplacian C v z =
        componentLaplacian C (fun y => U y.val) z - componentLaplacian C ℓ₀ z :=
          Rigidity.Steps.S3.componentLaplacian_sub C _ ℓ₀ z
      _ = 0 := by
        rw [componentLaplacian_restrict_eq C U z, hlapC z.val z.2, hℓ₀.1.1 z, sub_zero]
  have hvslope : componentSlopeAsymptotics C 0 v := by
    intro ε hε
    obtain ⟨R₁, hR₁, h₁⟩ := hu.2 (ε / 2) (half_pos hε)
    obtain ⟨R₂, -, h₂⟩ := hℓ₀.2 (ε / 2) (half_pos hε)
    refine ⟨max R₁ R₂, lt_max_of_lt_left hR₁, fun r hr z hz => ?_⟩
    have hzK := hCK z.2
    have f1 := abs_le.mp (h₁ r (le_of_max_le_left hr) ⟨z.val, hzK⟩
      (by rw [mem_componentEuclideanBall] at hz ⊢; exact hz))
    have f2 := abs_le.mp (h₂ r (le_of_max_le_right hr) z hz)
    have hsl : componentSlope K q ⟨z.val, hzK⟩ = componentSlope C q z := rfl
    have h0 : componentSlope C 0 z = 0 := by simp [componentSlope]
    have hvz : v z = (u ⟨z.val, hzK⟩ - componentSlope C q z) -
        (ℓ₀ z - componentSlope C q z) := by
      simp only [hv, hUK _ hzK]
      ring
    rw [hsl] at f1
    rw [h0, sub_zero, hvz, abs_le]
    constructor <;> linarith [f1.1, f1.2, f2.1, f2.2]
  obtain ⟨c, hc⟩ := hliou v hvlap hvslope
  have e := (hc ⟨w, hface hw⟩).trans (hc ⟨refSite d R, hface hz₀⟩).symm
  simp only [hv] at e
  exact hne (by linarith)

end Rigidity.Proofs.S4.OuterNonConstant
