import Rigidity.Proofs.S4.GadgetPlacement
import Rigidity.Steps.S4.NonConstantOnGadgetJoint
import Rigidity.Proofs.S3.SublinearLiouville
import LatticeProb.Network.OpenLadderConnected
import LatticeProb.Prob.Percolation.RootedHarmonicMeasurable

/-!
# Lemma 4.8: the attachment of the gadget

Step `step:4.8-attach` of Lemma 4.8 (paper L1411-1415 of the corrected draft, Figure
`attach-gadget`), `Rigidity.Steps.S4.AttachStep`, for the construction `H = attachBondSet`,
`τ = gadgetShift` of `Rigidity/Proofs/S4/GadgetPlacement.lean`.

Fix `R ≥ 5`, boundary placements `(x, x̃), (y, ỹ)` with `x ≠ y`, and write `ω̃ = closedNear R ω`
and `ω' = attachConfig R F ω` with `F = H ∪ {x x̃, y ỹ}`. Suppose that `ω̃` has a unique infinite
cluster `𝒞̃_∞ ∋ x̃, ỹ` with a corrected plane `ℓ̃_q`, `ℓ̃_q(x̃) ≠ ℓ̃_q(ỹ)`.

* The cluster. Every site of `H` is joined to `x` or `y` through `H` (the polygonal paths reach
  each of their sites, `chainBonds_reach`; the gadget is connected), so the cluster `𝒞'_∞` of `x̃`
  in `ω'` contains `𝒞̃_∞` and the sites of `F`. A cluster of `ω'` avoiding `𝒞'_∞` is a cluster of
  `ω̃` other than `𝒞̃_∞`, hence finite: `𝒞'_∞` is the unique infinite cluster of `ω'`, and
  `𝒞'_∞ ∩ Q_R = H` (`attach_conditioningEvent`).
* The Liouville argument (paper L1415). Let `ℓ'_q` be a corrected plane of `𝒞'_∞` and suppose it
  is constant on the gadget. On the path `P₁` from the low site to the terminal `s`, together with
  the partner `x̃` or `ỹ` of the low site, `ℓ'_q` is harmonic except at the partner, and the gadget
  neighbours of `s` carry the value of `s`; by the maximum principle on this finite connected set
  (`eq_of_harmonic_except`) `ℓ'_q` is constant there. The same holds for `P₂`, so
  `ℓ'_q(x) = ℓ'_q(x̃) = ℓ'_q(s) = ℓ'_q(t) = ℓ'_q(ỹ) = ℓ'_q(y)`. Then `ℓ'_q` restricted to `𝒞̃_∞`
  is harmonic, and `ℓ'_q - ℓ̃_q` is a sublinear harmonic function on `𝒞̃_∞`, constant by
  Theorem 2.4 at order zero (`Rigidity.Steps.S3.SublinearLiouvilleStep`): so
  `ℓ̃_q(x̃) = ℓ̃_q(ỹ)`, a contradiction.

The paper states the claim as `ℓ'_q(x) ≠ ℓ'_q(y)`; the argument above is the one the paper
indicates, with the values at `x̃, ỹ` and the gadget made explicit. Only the connectedness of
`P₁, P₂` is used, not that they are simple paths.

The almost sure inputs (the corrected planes of `SupercriticalBondCorrectorInput` and the
Liouville theorem) are applied to the finitely modified environments `ω̃` and `ω'` through the
finite energy bound `Rigidity.Steps.S4.finiteEnergyStep` (`ae_attachConfig`).
-/

namespace Rigidity.Proofs.S4

open MeasureTheory LatticeProb LatticeProb.Percolation LatticeProb.Network
  LatticeProb.Network.OpenLadder.Embedding Rigidity.Section4 Rigidity.Steps.S4

variable {d : ℕ}

/-! ### The polygonal paths reach each of their sites -/

theorem segmentBonds_subset {z : Vertex d} {j : Fin d} {u v w : ℤ} (hv1 : min u w ≤ v)
    (hv2 : v ≤ max u w) : segmentBonds z j u v ⊆ segmentBonds z j u w := by
  rintro e ⟨t, h1, h2, he⟩
  refine ⟨t, ?_, ?_, he⟩ <;> simp only [min_def, max_def] at * <;> split_ifs at * <;> omega

theorem mem_bondSites_segmentBonds {z c : Vertex d} {j : Fin d} {u w : ℤ}
    (hz : z ∈ bondSites (segmentBonds c j u w)) :
    ∃ v, min u w ≤ v ∧ v ≤ max u w ∧ z = Function.update c j v := by
  obtain ⟨e, ⟨t, h1, h2, he⟩, hze⟩ := hz
  rw [he, Sym2.mem_iff] at hze
  rcases hze with rfl | rfl
  · exact ⟨t, h1, h2.le, rfl⟩
  · exact ⟨t + 1, by omega, by omega, rfl⟩

/-- Every site of the staircase from `a` to `b` is reached from `a` along the staircase. -/
theorem stairBonds_reach {a b z : Vertex d} (hz : z ∈ bondSites (stairBonds a b)) :
    ∃ W : (nearestNeighborGraph d).Walk a z,
      ∀ e ∈ W.edges, ∃ f ∈ stairBonds a b, (f : Sym2 (Vertex d)) = e := by
  obtain ⟨e, he, hze⟩ := hz
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp he
  obtain ⟨v, hv1, hv2, rfl⟩ := mem_bondSites_segmentBonds ⟨e, hj, hze⟩
  obtain ⟨W, hW⟩ := stair_walk_aux a b j.val j.isLt.le
  have hc : stairCornerAfter a b j.val =
      Function.update (stairCorner a b j) j (a j) := by
    funext i
    by_cases hi : i = j
    · subst hi; simp [stairCornerAfter]
    · simp only [stairCornerAfter, Function.update_of_ne hi, stairCorner, Fin.lt_def]
  obtain ⟨S, hS⟩ := segment_walk (stairCorner a b j) j (a j) v
  refine ⟨W.append (S.copy hc.symm rfl), fun e he => ?_⟩
  rw [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_copy, List.mem_append] at he
  rcases he with he | he
  · exact hW e he
  · obtain ⟨f, hf, hfe⟩ := hS e he
    have hv1' : min (a j) (b j) ≤ v := hv1
    exact ⟨f, Set.mem_iUnion.mpr ⟨j, segmentBonds_subset hv1 hv2 hf⟩, hfe⟩

/-- Every site of the polygonal path through `a :: l` is reached from `a` along the path. -/
theorem chainBonds_reach : ∀ (a : Vertex d) (l : List (Vertex d)) (z : Vertex d),
    z ∈ bondSites (chainBonds (a :: l)) → ∃ W : (nearestNeighborGraph d).Walk a z,
      ∀ e ∈ W.edges, ∃ f ∈ chainBonds (a :: l), (f : Sym2 (Vertex d)) = e
  | a, [], z, hz => by
    obtain ⟨e, he, -⟩ := hz
    exact absurd he (by simp [chainBonds])
  | a, b :: l, z, hz => by
    obtain ⟨e, he, hze⟩ := hz
    rcases he with he | he
    · obtain ⟨W, hW⟩ := stairBonds_reach ⟨e, he, hze⟩
      exact ⟨W, fun e' he' => (hW e' he').imp fun f hf => ⟨Or.inl hf.1, hf.2⟩⟩
    · obtain ⟨W, hW⟩ := chainBonds_reach b l z ⟨e, he, hze⟩
      obtain ⟨S, hS⟩ := stair_walk a b
      refine ⟨S.append W, fun e' he' => ?_⟩
      rw [SimpleGraph.Walk.edges_append, List.mem_append] at he'
      rcases he' with he' | he'
      · exact (hS e' he').imp fun f hf => ⟨Or.inl hf.1, hf.2⟩
      · exact (hW e' he').imp fun f hf => ⟨Or.inr hf.1, hf.2⟩

/-- A lattice walk along open bonds is an open path. -/
theorem openGraph_reachable_of_walk {ω : Configuration d} {B : Set (Bond d)}
    (hB : ∀ f ∈ B, ω f = true) {a b : Vertex d} (W : (nearestNeighborGraph d).Walk a b)
    (hW : ∀ e ∈ W.edges, ∃ f ∈ B, (f : Sym2 (Vertex d)) = e) : (openGraph ω).Reachable a b := by
  induction W with
  | nil => rfl
  | @cons u v w h W ih =>
    refine SimpleGraph.Reachable.trans (SimpleGraph.Adj.reachable ⟨h, ?_⟩)
      (ih fun e he => hW e (by simp [he]))
    obtain ⟨f, hf, hfe⟩ := hW s(u, v) (by simp)
    have : f = bondOfAdjacent h := Subtype.ext hfe
    rw [← this]
    exact hB f hf

/-! ### Almost sure properties of the modified environments -/

/-- By finite energy, an almost sure property of the environment holds almost surely for the
environment with the bonds meeting `Q_R` reset to `F`. -/
theorem ae_attachConfig {p : unitInterval} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (R : ℕ)
    (F : Set (Bond d)) {Q : Configuration d → Prop} (h : ∀ᵐ ω ∂latticeBondLaw d p, Q ω) :
    ∀ᵐ ω ∂latticeBondLaw d p, Q (attachConfig R F ω) := by
  rw [ae_iff] at h ⊢
  have hfe := finiteEnergyStep (d := d) p R F {ω | ¬Q ω}
  rw [h, ENNReal.toReal_zero] at hfe
  have hm : 0 < min (p : ℝ) (1 - p) ^ (bondsNear d R).ncard :=
    pow_pos (lt_min hp0 (by linarith)) _
  have h0 : (latticeBondLaw d p (attachConfig R F ⁻¹' {ω | ¬Q ω})).toReal = 0 :=
    le_antisymm (le_of_mul_le_mul_left (by rw [mul_zero]; exact hfe) hm) ENNReal.toReal_nonneg
  exact ((ENNReal.toReal_eq_zero_iff _).mp h0).resolve_right (measure_ne_top _ _)

/-- Closing the bonds meeting `Q_R` is resetting them to `∅`. -/
theorem closedNear_eq_attachConfig (R : ℕ) (ω : Configuration d) :
    closedNear R ω = attachConfig R ∅ ω := by
  funext e
  simp [closedNear, attachConfig]

/-- The edges of a lattice walk along open bonds are open. -/
theorem edges_mem_openGraph {ω : Configuration d} {B : Set (Bond d)}
    (hB : ∀ f ∈ B, ω f = true) {a b : Vertex d} (W : (nearestNeighborGraph d).Walk a b)
    (hW : ∀ e ∈ W.edges, ∃ f ∈ B, (f : Sym2 (Vertex d)) = e) :
    ∀ e ∈ W.edges, e ∈ (openGraph ω).edgeSet := by
  intro e he
  have hl := W.edges_subset_edgeSet he
  obtain ⟨f, hf, hfe⟩ := hW e he
  induction e using Sym2.ind with
  | h u v =>
    have hadj : (nearestNeighborGraph d).Adj u v := hl
    refine ⟨hadj, ?_⟩
    have : f = bondOfAdjacent hadj := Subtype.ext hfe
    rw [← this]
    exact hB f hf

/-- The sites of a walk along the bonds of `B` are its start and sites of `B`. -/
theorem mem_support_of_walk {V : Type*} {G : SimpleGraph V} {B : Set (Sym2 V)} {a b : V}
    (W : G.Walk a b) (hW : ∀ e ∈ W.edges, e ∈ B) :
    ∀ v ∈ W.support, v = a ∨ ∃ e ∈ B, v ∈ e := by
  induction W with
  | nil => simp
  | @cons u v w h W ih =>
    intro z hz
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact Or.inl rfl
    · right
      rcases ih (fun e he => hW e (by simp [he])) z hz with rfl | hz'
      · exact ⟨s(u, z), hW _ (by simp), Sym2.mem_mk_right u z⟩
      · exact hz'

/-! ### The maximum principle on a finite set -/

theorem laplacian_neg {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] (U : V → ℝ) (z : V) :
    Graph.laplacian G (fun v => -U v) z = -Graph.laplacian G U z := by
  unfold Graph.laplacian
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem le_of_harmonic_except {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] {U : V → ℝ}
    {S : Set V} {b : V} (hS : S.Finite) (hb : b ∈ S)
    (hharm : ∀ z ∈ S, z ≠ b → Graph.laplacian G U z = 0)
    (hout : ∀ z ∈ S, z ≠ b → ∀ w, G.Adj z w → w ∈ S ∨ U w = U z)
    (hconn : ∀ z ∈ S, ∃ W : G.Walk z b, ∀ v ∈ W.support, v ∈ S) :
    ∀ z ∈ S, U z ≤ U b := by
  classical
  obtain ⟨m, hmS, hmax⟩ := Set.exists_max_image S U hS ⟨b, hb⟩
  have key : ∀ z c (W : G.Walk z c), c = b → (∀ v ∈ W.support, v ∈ S) → U z = U m →
      U b = U m := by
    intro z c W
    induction W with
    | nil => intro hc _ h; subst hc; exact h
    | @cons u v w h W ih =>
      intro hc hW hu
      have huS : u ∈ S := hW u (by simp)
      by_cases hub : u = b
      · subst hub; exact hu
      · have hle : ∀ y ∈ G.neighborFinset u, U y - U u ≤ 0 := by
          intro y hy
          rw [SimpleGraph.mem_neighborFinset] at hy
          rcases hout u huS hub y hy with hyS | hyu
          · rw [hu]; linarith [hmax y hyS]
          · rw [hyu, sub_self]
        have hz := (Finset.sum_eq_zero_iff_of_nonpos hle).mp (hharm u huS hub)
        have hv := hz v ((SimpleGraph.mem_neighborFinset _ _ _).mpr h)
        exact ih hc (fun t ht => hW t (by simp [ht])) (by linarith)
  intro z hz
  obtain ⟨W, hW⟩ := hconn m hmS
  rw [key m b W rfl hW rfl]
  exact hmax z hz

/-- **The maximum principle on a finite set, at equality.** A function harmonic at every site of
a finite set `S` but `b`, whose neighbours outside `S` carry its own value, and such that every
site of `S` is joined to `b` inside `S`, is constant on `S`. -/
theorem eq_of_harmonic_except {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] {U : V → ℝ}
    {S : Set V} {b : V} (hS : S.Finite) (hb : b ∈ S)
    (hharm : ∀ z ∈ S, z ≠ b → Graph.laplacian G U z = 0)
    (hout : ∀ z ∈ S, z ≠ b → ∀ w, G.Adj z w → w ∈ S ∨ U w = U z)
    (hconn : ∀ z ∈ S, ∃ W : G.Walk z b, ∀ v ∈ W.support, v ∈ S) :
    ∀ z ∈ S, U z = U b := by
  intro z hz
  refine le_antisymm (le_of_harmonic_except hS hb hharm hout hconn z hz) ?_
  have := le_of_harmonic_except (U := fun v => -U v) hS hb
    (fun z hz hzb => by rw [laplacian_neg, hharm z hz hzb, neg_zero])
    (fun z hz hzb w hw => (hout z hz hzb w hw).imp_right fun h => by rw [h]) hconn z hz
  linarith

/-- If two configurations have the same open bonds at `z`, except bonds to sites carrying the value
at `z`, their Laplacians agree at `z`. -/
theorem laplacian_eq_of_adj {ω₁ ω₂ : Configuration d} (U : Vertex d → ℝ) (z : Vertex d)
    (hle : ∀ w, (openGraph ω₁).Adj z w → (openGraph ω₂).Adj z w)
    (h : ∀ w, (openGraph ω₂).Adj z w → ¬(openGraph ω₁).Adj z w → U w = U z) :
    Graph.laplacian (openGraph ω₁) U z = Graph.laplacian (openGraph ω₂) U z := by
  classical
  unfold Graph.laplacian
  refine Finset.sum_subset (fun w hw => ?_) fun w hw2 hw1 => ?_
  · rw [SimpleGraph.mem_neighborFinset] at hw ⊢
    exact hle w hw
  · rw [SimpleGraph.mem_neighborFinset] at hw1 hw2
    rw [h w hw2 hw1, sub_self]

/-! ### The environments `ω̃` and `ω'` -/

section Env

open scoped Classical

variable {R : ℕ} {F : Set (Bond d)} {ω : Configuration d}

theorem cube_finite (d R : ℕ) : (cube d R).Finite :=
  (Set.finite_Icc (fun _ => -(R : ℤ)) (fun _ => (R : ℤ))).subset fun _ hy =>
    ⟨fun i => (abs_le.mp (hy i)).1, fun i => (abs_le.mp (hy i)).2⟩

theorem attachConfig_of_mem {e : Bond d} (he : e ∈ bondsNear d R) :
    attachConfig R F ω e = decide (e ∈ F) := by simp [attachConfig, he]

theorem attachConfig_of_not_mem {e : Bond d} (he : e ∉ bondsNear d R) :
    attachConfig R F ω e = ω e := by simp [attachConfig, he]

theorem mem_bondsNear_of_mem {e : Bond d} {z : Vertex d} (hz : z ∈ (e : Sym2 (Vertex d)))
    (hzR : z ∈ cube d R) : e ∈ bondsNear d R := ⟨z, hz, hzR⟩

/-- The bonds of `F` meeting `Q_R` are open in `ω'`. -/
theorem attachConfig_eq_true {e : Bond d} {z : Vertex d} (hz : z ∈ (e : Sym2 (Vertex d)))
    (hzR : z ∈ cube d R) (he : e ∈ F) : attachConfig R F ω e = true := by
  rw [attachConfig_of_mem (mem_bondsNear_of_mem hz hzR)]
  simpa using he

/-- The open bonds of `ω̃` avoid `Q_R` and are open in `ω'`. -/
theorem closedNear_adj {a b : Vertex d} (h : (openGraph (closedNear R ω)).Adj a b) :
    a ∉ cube d R ∧ (openGraph (attachConfig R F ω)).Adj a b := by
  obtain ⟨hab, ho⟩ := h
  have hn : bondOfAdjacent hab ∉ bondsNear d R := by
    intro hn
    simp [closedNear, hn] at ho
  refine ⟨fun ha => hn (mem_bondsNear_of_mem (Sym2.mem_mk_left a b) ha), hab, ?_⟩
  rw [attachConfig_of_not_mem hn]
  simpa [closedNear, hn] using ho

/-- An open bond of `ω'` is open in `ω̃` or belongs to `F`. -/
theorem attachConfig_adj {a b : Vertex d} (h : (openGraph (attachConfig R F ω)).Adj a b) :
    (openGraph (closedNear R ω)).Adj a b ∨
      ∃ h : (nearestNeighborGraph d).Adj a b, bondOfAdjacent h ∈ F := by
  obtain ⟨hab, ho⟩ := h
  by_cases hn : bondOfAdjacent hab ∈ bondsNear d R
  · rw [attachConfig_of_mem hn] at ho
    exact Or.inr ⟨hab, of_decide_eq_true ho⟩
  · rw [attachConfig_of_not_mem hn] at ho
    exact Or.inl ⟨hab, by simp [closedNear, hn, ho]⟩

theorem closedNear_le_attachConfig :
    openGraph (closedNear R ω) ≤ openGraph (attachConfig R F ω) :=
  fun _ _ h => (closedNear_adj h).2

/-- A site of `Q_R` is isolated in `ω̃`, so an infinite cluster of `ω̃` avoids `Q_R`. -/
theorem not_mem_cube_of_infinite {C : OpenComponent (closedNear R ω)} (hC : C.supp.Infinite)
    {z : Vertex d} (hz : z ∈ C.supp) : z ∉ cube d R := by
  intro hzQ
  apply hC
  refine (Set.finite_singleton z).subset fun w hw => ?_
  obtain ⟨W⟩ := SimpleGraph.ConnectedComponent.exact
    (((SimpleGraph.ConnectedComponent.mem_supp_iff C z).mp hz).trans
      ((SimpleGraph.ConnectedComponent.mem_supp_iff C w).mp hw).symm)
  cases W with
  | nil => exact Set.mem_singleton _
  | cons h _ => exact absurd hzQ (closedNear_adj (F := ∅) h).1

end Env

/-! ### The attached cluster -/

section Attached

open scoped Classical

variable {hd : 2 ≤ d} {R : ℕ} {x x' y y' : Vertex d}

/-- The environment `ω'` of the attachment of `H R x y` through the bonds `x x̃`, `y ỹ`. -/
noncomputable abbrev attachedEnv (hd : 2 ≤ d) (R : ℕ) (x x' y y' : Vertex d)
    (ω : Configuration d) : Configuration d :=
  attachConfig R (attachBonds (attachBondSet hd R x y) x x' y y') ω

/-- The bonds of `H` lie in `Q_R`. -/
theorem attachBondSet_cube (hR : 4 ≤ R) (hx : (x, x') ∈ boundaryPairs d R)
    (hy : (y, y') ∈ boundaryPairs d R) :
    ∀ e ∈ attachBondSet hd R x y, ∀ z ∈ (e : Sym2 (Vertex d)), z ∈ cube d R := by
  intro e he z hz
  rcases he with (he | he) | he
  · have := gadget_mem_cube hd hR (he z hz)
    rwa [add_sub_cancel] at this
  · exact chainBonds_cube (attachWaypoints_cube hR _ (Or.inr rfl) (by norm_num)
      (lowSite_mem hx.1 hy.1)) e he z hz
  · exact chainBonds_cube (attachWaypoints_cube hR _ (Or.inl rfl) (by norm_num)
      (highSite_mem hx.1 hy.1)) e he z hz

/-- The low and high sites are `x, y` in some order. -/
theorem lowSite_highSite_cases (x y : Vertex d) :
    (lowSite hd x y = x ∧ highSite hd x y = y) ∨ (lowSite hd x y = y ∧ highSite hd x y = x) := by
  unfold lowSite highSite
  split_ifs <;> simp

theorem mem_attachBonds_cases {e : Bond d}
    (he : e ∈ attachBonds (attachBondSet hd R x y) x x' y y') :
    e ∈ gadgetBonds hd R ∨ e ∈ lowPathBonds hd R x y ∨ e ∈ highPathBonds hd R x y ∨
      (e : Sym2 (Vertex d)) = s(x, x') ∨ (e : Sym2 (Vertex d)) = s(y, y') := by
  rcases he with ((he | he) | he) | he | he <;> tauto

/-- The bonds of `F = H ∪ {x x̃, y ỹ}` are open in `ω'`. -/
theorem attachBonds_open (hR : 4 ≤ R) (hx : (x, x') ∈ boundaryPairs d R)
    (hy : (y, y') ∈ boundaryPairs d R) (ω : Configuration d) :
    ∀ f ∈ attachBonds (attachBondSet hd R x y) x x' y y',
      attachedEnv hd R x x' y y' ω f = true := by
  intro f hf
  rcases hf with hf | hf | hf
  · obtain ⟨a, b, hab, -⟩ := f.2
    have ha : a ∈ (f : Sym2 (Vertex d)) := by rw [hab]; exact Sym2.mem_mk_left a b
    exact attachConfig_eq_true ha (attachBondSet_cube hR hx hy f hf a ha) (Or.inl hf)
  · exact attachConfig_eq_true (by rw [hf]; exact Sym2.mem_mk_left x x') hx.1 (Or.inr (Or.inl hf))
  · exact attachConfig_eq_true (by rw [hf]; exact Sym2.mem_mk_left y y') hy.1 (Or.inr (Or.inr hf))

/-- The translated gadget is connected in `ω'`. -/
theorem gadget_reachable (hR : 4 ≤ R) (ω : Configuration d) {g g' : Vertex d}
    (hg : g ∈ ambientSites hd (R : ℤ)) (hg' : g' ∈ ambientSites hd (R : ℤ)) :
    (openGraph (attachedEnv hd R x x' y y' ω)).Reachable (gadgetShift d R + g)
      (gadgetShift d R + g') := by
  let φ : ambientGraph hd (R : ℤ) →g openGraph (attachedEnv hd R x x' y y' ω) :=
    { toFun := fun g => gadgetShift d R + g.val
      map_rel' := fun {a b} hab => by
        have hadj : (nearestNeighborGraph d).Adj (gadgetShift d R + a.val)
            (gadgetShift d R + b.val) := by
          rw [add_comm (gadgetShift d R) a.val, add_comm (gadgetShift d R) b.val,
            nearestNeighborGraph_adj_add_iff]
          exact hab
        refine ⟨hadj, attachConfig_eq_true (Sym2.mem_mk_left _ _) (gadget_mem_cube hd hR a.2)
          (Or.inl (Or.inl (Or.inl ?_)))⟩
        intro z hz
        simp only [bondOfAdjacent, Sym2.mem_iff] at hz
        rcases hz with rfl | rfl
        · simp
        · simp }
  have hconn : (ambientGraph hd (R : ℤ)).Connected :=
    (ambientIso hd (R : ℤ)).connected_iff.mp (OpenLadder.connected (by omega))
  exact (hconn.preconnected ⟨g, hg⟩ ⟨g', hg'⟩).map φ

theorem zeroPad_terminal_s (R : ℕ) :
    zeroPad d (-2, -halfSide R - 1) = gadgetShift d R + zeroPad d (1, 1) := by
  funext i
  simp only [gadgetShift, zeroPad, Pi.add_apply]
  split_ifs <;> ring

theorem zeroPad_terminal_t (R : ℕ) :
    zeroPad d (1, -halfSide R - 1) = gadgetShift d R + zeroPad d (4, 1) := by
  funext i
  simp only [gadgetShift, zeroPad, Pi.add_apply]
  split_ifs <;> ring

theorem zeroPad_one_one_mem (hd : 2 ≤ d) (R : ℕ) : zeroPad d (1, 1) ∈ ambientSites hd (R : ℤ) :=
  ⟨Or.inl ⟨by rw [zeroPad_zero hd], by rw [zeroPad_zero hd]; norm_num, by rw [zeroPad_one hd]⟩,
    fun i hi => zeroPad_extra _ i hi⟩

theorem zeroPad_four_one_mem (hd : 2 ≤ d) (R : ℕ) : zeroPad d (4, 1) ∈ ambientSites hd (R : ℤ) :=
  ⟨Or.inl ⟨by rw [zeroPad_zero hd]; norm_num, by rw [zeroPad_zero hd], by rw [zeroPad_one hd]⟩,
    fun i hi => zeroPad_extra _ i hi⟩

/-- A site of `∂Q_R` is not a terminal of the gadget. -/
theorem boundary_ne_zeroPad (hR : 5 ≤ R) {z z' : Vertex d} (hz : (z, z') ∈ boundaryPairs d R)
    {c : ℤ} (hc : -2 ≤ c ∧ c ≤ 1) : z ≠ zeroPad d (c, -halfSide R - 1) := by
  intro heq
  obtain ⟨i, hi⟩ := boundaryPairs_extreme hz
  have h3 : zeroPad d (c, -halfSide R - 1) i = c ∨
      zeroPad d (c, -halfSide R - 1) i = -halfSide R - 1 ∨
      zeroPad d (c, -halfSide R - 1) i = 0 := by
    unfold zeroPad
    split_ifs <;> simp
  have hm : 0 ≤ halfSide R ∧ 2 * halfSide R ≤ R := by unfold halfSide; omega
  rw [← heq] at h3
  omega

/-- The paths: `P₁` joins the low site to `s`, `P₂` the high site to `t`, and both ends are sites of
the path. -/
theorem lowPath_ends (hR : 5 ≤ R) (hx : (x, x') ∈ boundaryPairs d R)
    (hy : (y, y') ∈ boundaryPairs d R) :
    lowSite hd x y ∈ bondSites (lowPathBonds hd R x y) ∧
      zeroPad d (-2, -halfSide R - 1) ∈ bondSites (lowPathBonds hd R x y) := by
  obtain ⟨W, -, hW⟩ := lowPath_walk hd R x y
  have hne : lowSite hd x y ≠ zeroPad d (-2, -halfSide R - 1) := by
    rcases lowSite_highSite_cases (hd := hd) x y with ⟨hl, -⟩ | ⟨hl, -⟩ <;> rw [hl]
    · exact boundary_ne_zeroPad hR hx (by norm_num)
    · exact boundary_ne_zeroPad hR hy (by norm_num)
  have key : ∀ (W' : (nearestNeighborGraph d).Walk (lowSite hd x y)
      (zeroPad d (-2, -halfSide R - 1))) (_ : ∀ e ∈ W'.edges, ∃ f ∈ lowPathBonds hd R x y,
        (f : Sym2 (Vertex d)) = e),
      ∀ v ∈ W'.support, v = lowSite hd x y ∨ v ∈ bondSites (lowPathBonds hd R x y) := by
    intro W' hW' v hv
    rcases mem_support_of_walk
      (B := {e | ∃ f ∈ lowPathBonds hd R x y, (f : Sym2 (Vertex d)) = e}) W'
      hW' v hv with h | ⟨e, ⟨f, hf, rfl⟩, hve⟩
    · exact Or.inl h
    · exact Or.inr ⟨f, hf, hve⟩
  refine ⟨?_, (key W hW _ W.end_mem_support).resolve_left (Ne.symm hne)⟩
  rcases mem_support_of_walk (B := {e | ∃ f ∈ lowPathBonds hd R x y, (f : Sym2 (Vertex d)) = e})
      W.reverse (fun e he => hW e (by simpa using he)) _ W.reverse.end_mem_support with
    h | ⟨e, ⟨f, hf, rfl⟩, hve⟩
  · exact absurd h hne
  · exact ⟨f, hf, hve⟩

theorem highPath_ends (hR : 5 ≤ R) (hx : (x, x') ∈ boundaryPairs d R)
    (hy : (y, y') ∈ boundaryPairs d R) :
    highSite hd x y ∈ bondSites (highPathBonds hd R x y) ∧
      zeroPad d (1, -halfSide R - 1) ∈ bondSites (highPathBonds hd R x y) := by
  obtain ⟨W, -, hW⟩ := highPath_walk hd R x y
  have hne : highSite hd x y ≠ zeroPad d (1, -halfSide R - 1) := by
    rcases lowSite_highSite_cases (hd := hd) x y with ⟨-, hh⟩ | ⟨-, hh⟩ <;> rw [hh]
    · exact boundary_ne_zeroPad hR hy (by norm_num)
    · exact boundary_ne_zeroPad hR hx (by norm_num)
  have key : ∀ (W' : (nearestNeighborGraph d).Walk (highSite hd x y)
      (zeroPad d (1, -halfSide R - 1))) (_ : ∀ e ∈ W'.edges, ∃ f ∈ highPathBonds hd R x y,
        (f : Sym2 (Vertex d)) = e),
      ∀ v ∈ W'.support, v = highSite hd x y ∨ v ∈ bondSites (highPathBonds hd R x y) := by
    intro W' hW' v hv
    rcases mem_support_of_walk
      (B := {e | ∃ f ∈ highPathBonds hd R x y, (f : Sym2 (Vertex d)) = e}) W'
      hW' v hv with h | ⟨e, ⟨f, hf, rfl⟩, hve⟩
    · exact Or.inl h
    · exact Or.inr ⟨f, hf, hve⟩
  refine ⟨?_, (key W hW _ W.end_mem_support).resolve_left (Ne.symm hne)⟩
  rcases mem_support_of_walk (B := {e | ∃ f ∈ highPathBonds hd R x y, (f : Sym2 (Vertex d)) = e})
      W.reverse (fun e he => hW e (by simpa using he)) _ W.reverse.end_mem_support with
    h | ⟨e, ⟨f, hf, rfl⟩, hve⟩
  · exact absurd h hne
  · exact ⟨f, hf, hve⟩

/-- In `ω'`, the site `x̃` reaches every site of `F = H ∪ {x x̃, y ỹ}` and of the gadget. -/
theorem attached_reachable (hR : 5 ≤ R) (hx : (x, x') ∈ boundaryPairs d R)
    (hy : (y, y') ∈ boundaryPairs d R) (ω : Configuration d) :
    (∀ z ∈ bondSites (attachBonds (attachBondSet hd R x y) x x' y y'),
      (openGraph (attachedEnv hd R x x' y y' ω)).Reachable x' z) ∧
    ∀ g ∈ ambientSites hd (R : ℤ),
      (openGraph (attachedEnv hd R x x' y y' ω)).Reachable x' (gadgetShift d R + g) := by
  set G' := openGraph (attachedEnv hd R x x' y y' ω)
  have hopen := attachBonds_open (hd := hd) (by omega : 4 ≤ R) hx hy ω
  have hxx' : G'.Adj x x' := ⟨hx.2.2, hopen _ (Or.inr (Or.inl rfl))⟩
  have hyy' : G'.Adj y y' := ⟨hy.2.2, hopen _ (Or.inr (Or.inr rfl))⟩
  have hlow : ∀ z ∈ bondSites (lowPathBonds hd R x y), G'.Reachable (lowSite hd x y) z := by
    intro z hz
    obtain ⟨W, hW⟩ := chainBonds_reach _ _ z hz
    exact openGraph_reachable_of_walk (fun f hf => hopen f (Or.inl (Or.inl (Or.inr hf)))) W hW
  have hhigh : ∀ z ∈ bondSites (highPathBonds hd R x y), G'.Reachable (highSite hd x y) z := by
    intro z hz
    obtain ⟨W, hW⟩ := chainBonds_reach _ _ z hz
    exact openGraph_reachable_of_walk (fun f hf => hopen f (Or.inl (Or.inr hf))) W hW
  have hgad : ∀ g ∈ ambientSites hd (R : ℤ),
      G'.Reachable (zeroPad d (-2, -halfSide R - 1)) (gadgetShift d R + g) := fun g hg => by
    rw [zeroPad_terminal_s]
    exact gadget_reachable (by omega) ω (zeroPad_one_one_mem hd R) hg
  have hlos := hlow _ (lowPath_ends (hd := hd) hR hx hy).2
  have hhit := hhigh _ (highPath_ends (hd := hd) hR hx hy).2
  have hst : G'.Reachable (zeroPad d (-2, -halfSide R - 1)) (zeroPad d (1, -halfSide R - 1)) := by
    rw [zeroPad_terminal_t]
    exact hgad _ (zeroPad_four_one_mem hd R)
  have hxy : G'.Reachable x y := by
    rcases lowSite_highSite_cases (hd := hd) x y with ⟨hl, hh⟩ | ⟨hl, hh⟩
    · rw [hl] at hlos; rw [hh] at hhit
      exact hlos.trans (hst.trans hhit.symm)
    · rw [hl] at hlos; rw [hh] at hhit
      exact (hhit.trans (hst.symm.trans hlos.symm))
  have hx'x : G'.Reachable x' x := hxx'.symm.reachable
  have hx'y : G'.Reachable x' y := hx'x.trans hxy
  have hlo : G'.Reachable x' (lowSite hd x y) := by
    rcases lowSite_highSite_cases (hd := hd) x y with ⟨hl, -⟩ | ⟨hl, -⟩ <;> rw [hl]
    · exact hx'x
    · exact hx'y
  have hhi : G'.Reachable x' (highSite hd x y) := by
    rcases lowSite_highSite_cases (hd := hd) x y with ⟨-, hh⟩ | ⟨-, hh⟩ <;> rw [hh]
    · exact hx'y
    · exact hx'x
  have hgad' : ∀ g ∈ ambientSites hd (R : ℤ), G'.Reachable x' (gadgetShift d R + g) :=
    fun g hg => (hlo.trans hlos).trans (hgad g hg)
  refine ⟨fun z hz => ?_, hgad'⟩
  obtain ⟨e, he, hze⟩ := hz
  rcases mem_attachBonds_cases he with he | he | he | he | he
  · have := hgad' _ (he z hze)
    rwa [add_sub_cancel] at this
  · exact hlo.trans (hlow z ⟨e, he, hze⟩)
  · exact hhi.trans (hhigh z ⟨e, he, hze⟩)
  · rw [he, Sym2.mem_iff] at hze
    rcases hze with rfl | rfl
    · exact hx'x
    · rfl
  · rw [he, Sym2.mem_iff] at hze
    rcases hze with rfl | rfl
    · exact hx'y
    · exact hx'y.trans hyy'.reachable

/-- **The attached cluster.** If `ω̃` has a unique infinite cluster `𝒞̃_∞ ∋ x̃`, then `ω'` has a
unique infinite cluster; it contains `x̃`, `𝒞̃_∞`, the sites of `F` and the translated gadget. -/
theorem attached_unique (hR : 5 ≤ R) (hx : (x, x') ∈ boundaryPairs d R)
    (hy : (y, y') ∈ boundaryPairs d R) {ω : Configuration d}
    (h : HasUniqueInfiniteOpenComponent (closedNear R ω))
    (hx' : x' ∈ (uniqueInfiniteComponent h).supp) :
    ∃ h' : HasUniqueInfiniteOpenComponent (attachedEnv hd R x x' y y' ω),
      x' ∈ (uniqueInfiniteComponent h').supp ∧
      ∀ z, (openGraph (attachedEnv hd R x x' y y' ω)).Reachable x' z ∨
        z ∈ (uniqueInfiniteComponent h).supp → z ∈ (uniqueInfiniteComponent h').supp := by
  set G' := openGraph (attachedEnv hd R x x' y y' ω)
  set G := openGraph (closedNear R ω)
  set K := G'.connectedComponentMk x'
  have memK : ∀ z, G'.Reachable x' z → z ∈ K.supp := fun z hz =>
    (SimpleGraph.ConnectedComponent.mem_supp_iff K z).mpr
      (SimpleGraph.ConnectedComponent.sound hz.symm)
  have hC : ∀ z ∈ (uniqueInfiniteComponent h).supp, G'.Reachable x' z := fun z hz =>
    (SimpleGraph.ConnectedComponent.exact
      (((SimpleGraph.ConnectedComponent.mem_supp_iff _ x').mp hx').trans
        ((SimpleGraph.ConnectedComponent.mem_supp_iff _ z).mp hz).symm)).mono
      closedNear_le_attachConfig
  have hKinf : K.supp.Infinite :=
    (uniqueInfiniteComponent_infinite h).mono fun z hz => memK z (hC z hz)
  have hback : ∀ z w, z ∉ K.supp → G'.Reachable z w → G.Reachable z w := by
    intro z w hz ⟨W⟩
    induction W with
    | nil => rfl
    | @cons u v w' hadj W ih =>
      rcases attachConfig_adj hadj with h' | ⟨hab, hF⟩
      · have hv : v ∉ K.supp := fun hv => hz (K.mem_supp_of_adj_mem_supp hv hadj.symm)
        exact h'.reachable.trans (ih hv)
      · exact absurd (memK u ((attached_reachable hR hx hy ω).1 u
          ⟨_, hF, Sym2.mem_mk_left u v⟩)) hz
  have huniq : ∀ K₂ : OpenComponent (attachedEnv hd R x x' y y' ω), K₂.supp.Infinite → K₂ = K := by
    intro K₂ hK₂
    obtain ⟨z, hz⟩ := hK₂.nonempty
    have hz' := (SimpleGraph.ConnectedComponent.mem_supp_iff K₂ z).mp hz
    by_cases hzK : z ∈ K.supp
    · exact hz'.symm.trans ((SimpleGraph.ConnectedComponent.mem_supp_iff K z).mp hzK)
    · exfalso
      set C₂ := G.connectedComponentMk z
      have hsub : K₂.supp ⊆ C₂.supp := fun w hw => by
        have hr : G'.Reachable z w := SimpleGraph.ConnectedComponent.exact
          (hz'.trans ((SimpleGraph.ConnectedComponent.mem_supp_iff K₂ w).mp hw).symm)
        exact (SimpleGraph.ConnectedComponent.mem_supp_iff C₂ w).mpr
          (SimpleGraph.ConnectedComponent.sound (hback z w hzK hr).symm)
      have hC₂ : C₂ = uniqueInfiniteComponent h :=
        (eq_uniqueInfiniteComponent_iff h C₂).mpr (hK₂.mono hsub)
      have hx'C₂ : x' ∈ C₂.supp := hC₂ ▸ hx'
      have hr : G.Reachable z x' := SimpleGraph.ConnectedComponent.exact
        ((SimpleGraph.ConnectedComponent.mem_supp_iff C₂ x').mp hx'C₂).symm
      exact hzK (memK z (hr.mono closedNear_le_attachConfig).symm)
  have hU : HasUniqueInfiniteOpenComponent (attachedEnv hd R x x' y y' ω) := ⟨K, hKinf, huniq⟩
  have hKeq : uniqueInfiniteComponent hU = K :=
    ((eq_uniqueInfiniteComponent_iff hU K).mpr hKinf).symm
  refine ⟨hU, ?_, ?_⟩ <;> rw [hKeq]
  · exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  · rintro z (hz | hz)
    · exact memK z hz
    · exact memK z (hC z hz)

/-- **`𝒞'_∞ ∩ Q_R = H`.** -/
theorem attached_componentBondsIn (hR : 5 ≤ R) (hx : (x, x') ∈ boundaryPairs d R)
    (hy : (y, y') ∈ boundaryPairs d R) {ω : Configuration d}
    (K : OpenComponent (attachedEnv hd R x x' y y' ω))
    (hK : ∀ z ∈ bondSites (attachBondSet hd R x y), z ∈ K.supp) :
    componentBondsIn K (cube d R) = attachBondSet hd R x y := by
  ext e
  constructor
  · rintro ⟨he, hz⟩
    obtain ⟨a, b, hab, -⟩ := e.2
    have ha : a ∈ (e : Sym2 (Vertex d)) := by rw [hab]; exact Sym2.mem_mk_left a b
    rw [attachedEnv, attachConfig_of_mem (mem_bondsNear_of_mem ha (hz a ha).1)] at he
    rcases of_decide_eq_true he with heH | he' | he'
    · exact heH
    · exact absurd (hz x' (by rw [he']; exact Sym2.mem_mk_right x x')).1 hx.2.1
    · exact absurd (hz y' (by rw [he']; exact Sym2.mem_mk_right y y')).1 hy.2.1
  · intro he
    exact ⟨attachBonds_open (by omega) hx hy ω e (Or.inl he), fun z hz =>
      ⟨attachBondSet_cube (by omega) hx hy e he z hz, hK z ⟨e, he, hz⟩⟩⟩

/-- **The maximum principle on a path.** Let `U` be harmonic in `ω'` at the sites of a finite bond
set `P` whose sites are reached from `a` along `P`, joined to `a'` by an open bond, and whose open
neighbours are sites of `P`, the site `a'`, or carry the value of the site. Then `U` equals
`U a'` on the sites of `P`. -/
theorem path_value_eq {ω' : Configuration d} {U : Vertex d → ℝ} {P : Set (Bond d)}
    {a a' : Vertex d} (hfin : (bondSites P).Finite) (hadj : (openGraph ω').Adj a a')
    (hreach : ∀ z ∈ bondSites P, ∃ W : (nearestNeighborGraph d).Walk a z,
      ∀ e ∈ W.edges, ∃ f ∈ P, (f : Sym2 (Vertex d)) = e)
    (hopen : ∀ f ∈ P, ω' f = true)
    (hharm : ∀ z ∈ bondSites P, Graph.laplacian (openGraph ω') U z = 0)
    (hout : ∀ z ∈ bondSites P, ∀ w, (openGraph ω').Adj z w →
      w ∈ bondSites P ∨ w = a' ∨ U w = U z) :
    ∀ z ∈ bondSites P, U z = U a' := by
  have hS : ∀ z ∈ insert a' (bondSites P), z ≠ a' → z ∈ bondSites P := fun z hz hza =>
    (Set.mem_insert_iff.mp hz).resolve_left hza
  refine fun z hz => eq_of_harmonic_except (hfin.insert a') (Set.mem_insert _ _)
    (fun z hz hza => hharm z (hS z hz hza))
    (fun z hz hza w hw => ?_) (fun z hz => ?_) z (Set.mem_insert_of_mem _ hz)
  · rcases hout z (hS z hz hza) w hw with h | h | h
    · exact Or.inl (Set.mem_insert_of_mem _ h)
    · exact Or.inl (h ▸ Set.mem_insert _ _)
    · exact Or.inr h
  · rcases Set.mem_insert_iff.mp hz with rfl | hz
    · exact ⟨SimpleGraph.Walk.nil, by simp⟩
    · obtain ⟨W, hW⟩ := hreach z hz
      let W' := W.transfer (openGraph ω') (edges_mem_openGraph hopen W hW)
      refine ⟨W'.reverse.concat hadj, fun v hv => ?_⟩
      rw [SimpleGraph.Walk.support_concat, List.mem_append,
        SimpleGraph.Walk.support_reverse, List.mem_reverse, SimpleGraph.Walk.support_transfer,
        List.mem_singleton] at hv
      rcases hv with hv | rfl
      · rcases mem_support_of_walk (B := {e | ∃ f ∈ P, (f : Sym2 (Vertex d)) = e}) W hW v hv with
          rfl | ⟨e, ⟨f, hf, rfl⟩, hve⟩
        · rcases mem_support_of_walk (B := {e | ∃ f ∈ P, (f : Sym2 (Vertex d)) = e}) W.reverse
            (fun e he => hW e (by simpa using he)) _ W.reverse.end_mem_support with
            h | ⟨e, ⟨f, hf, rfl⟩, hve⟩
          · exact Set.mem_insert_of_mem _ (by rw [h]; exact hz)
          · exact Set.mem_insert_of_mem _ ⟨f, hf, hve⟩
        · exact Set.mem_insert_of_mem _ ⟨f, hf, hve⟩
      · exact Set.mem_insert _ _

/-- The open neighbours in `ω'` of a site of a path `P ∈ {P₁, P₂}`: sites of `P`, the partner `a'`
of its boundary site, or sites of the gadget carrying the gadget value (when `U` is constant on the
gadget). -/
theorem path_out (hR : 5 ≤ R) (hx : (x, x') ∈ boundaryPairs d R)
    (hy : (y, y') ∈ boundaryPairs d R) (hxy : x ≠ y) {ω : Configuration d} {U : Vertex d → ℝ}
    (hgad : ∀ z w, z - gadgetShift d R ∈ ambientSites hd (R : ℤ) →
      w - gadgetShift d R ∈ ambientSites hd (R : ℤ) → U z = U w)
    {P Q : Set (Bond d)}
    (hPQ : (P = lowPathBonds hd R x y ∧ Q = highPathBonds hd R x y) ∨
      (P = highPathBonds hd R x y ∧ Q = lowPathBonds hd R x y))
    {a' : Vertex d} (ha' : (a' = x' ∧ y ∈ bondSites Q) ∨ (a' = y' ∧ x ∈ bondSites Q))
    {z w : Vertex d} (hz : z ∈ bondSites P)
    (hzw : (openGraph (attachedEnv hd R x x' y y' ω)).Adj z w) :
    w ∈ bondSites P ∨ w = a' ∨ U w = U z := by
  have hdisj : Disjoint (bondSites P) (bondSites Q) := by
    rcases hPQ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (attachPaths_spec hd hR hx hy hxy).1
    · exact (attachPaths_spec hd hR hx hy hxy).1.symm
  have hzQ : z ∉ bondSites Q := Set.disjoint_left.mp hdisj hz
  have hzR : z ∈ cube d R := by
    obtain ⟨e, he, hze⟩ := hz
    have hPH : e ∈ attachBondSet hd R x y := by
      rcases hPQ with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact Or.inl (Or.inr he)
      · exact Or.inr he
    exact attachBondSet_cube (by omega) hx hy e hPH z hze
  rcases attachConfig_adj hzw with h | ⟨hab, hF⟩
  · exact absurd hzR (closedNear_adj (F := ∅) h).1
  rcases mem_attachBonds_cases hF with hg | hl | hh | he | he
  · exact Or.inr (Or.inr (hgad w z (hg w (Sym2.mem_mk_right z w)) (hg z (Sym2.mem_mk_left z w))))
  · rcases hPQ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨_, hl, Sym2.mem_mk_right z w⟩
    · exact absurd ⟨_, hl, Sym2.mem_mk_left z w⟩ hzQ
  · rcases hPQ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd ⟨_, hh, Sym2.mem_mk_left z w⟩ hzQ
    · exact Or.inl ⟨_, hh, Sym2.mem_mk_right z w⟩
  · rcases Sym2.eq_iff.mp he with ⟨hzx, hwx⟩ | ⟨hzx, -⟩
    · rcases ha' with ⟨ha', -⟩ | ⟨-, hxQ⟩
      · exact Or.inr (Or.inl (hwx.trans ha'.symm))
      · exact absurd (hzx ▸ hxQ) hzQ
    · exact absurd (hzx ▸ hzR) hx.2.1
  · rcases Sym2.eq_iff.mp he with ⟨hzy, hwy⟩ | ⟨hzy, -⟩
    · rcases ha' with ⟨-, hyQ⟩ | ⟨ha', -⟩
      · exact absurd (hzy ▸ hyQ) hzQ
      · exact Or.inr (Or.inl (hwy.trans ha'.symm))
    · exact absurd (hzy ▸ hzR) hy.2.1

/-- **The Liouville argument** (paper L1415). Let `𝒞̃_∞ ∋ x̃, ỹ` be the unique infinite cluster of
`ω̃`, with a corrected plane `ℓ̃_q`, `ℓ̃_q(x̃) ≠ ℓ̃_q(ỹ)`, on which sublinear harmonic functions are
constant. Then every corrected plane `ℓ'_q` of the attached cluster `𝒞'_∞` is not constant on the
gadget. -/
theorem attached_gadget_nonconstant (hR : 5 ≤ R) (hx : (x, x') ∈ boundaryPairs d R)
    (hy : (y, y') ∈ boundaryPairs d R) (hxy : x ≠ y) {ω : Configuration d} {q : Fin d → ℝ}
    (C : OpenComponent (closedNear R ω)) (hCinf : C.supp.Infinite)
    (hx' : x' ∈ C.supp) (hy' : y' ∈ C.supp)
    (ũ : C → ℝ) (hũ : IsCorrectedPlane C q ũ)
    (hne : ũ ⟨x', hx'⟩ ≠ ũ ⟨y', hy'⟩)
    (hliou : ∀ v : C → ℝ,
      (∀ z, componentLaplacian C v z = 0) →
      componentSlopeAsymptotics C 0 v → ∃ c : ℝ, ∀ z, v z = c)
    (K : OpenComponent (attachedEnv hd R x x' y y' ω))
    (hK : ∀ z, (openGraph (attachedEnv hd R x x' y y' ω)).Reachable x' z ∨
        z ∈ C.supp → z ∈ K.supp)
    (u : K → ℝ) (hu : IsCorrectedPlane K q u) :
    ∃ g ∈ ambientSites hd (R : ℤ), ∃ g' ∈ ambientSites hd (R : ℤ),
      ∃ hg : gadgetShift d R + g ∈ K.supp, ∃ hg' : gadgetShift d R + g' ∈ K.supp,
        u ⟨gadgetShift d R + g, hg⟩ ≠ u ⟨gadgetShift d R + g', hg'⟩ := by
  have hreach := attached_reachable (hd := hd) hR hx hy ω
  have hgK : ∀ g ∈ ambientSites hd (R : ℤ), gadgetShift d R + g ∈ K.supp :=
    fun g hg => hK _ (Or.inl (hreach.2 g hg))
  have hFK : ∀ z ∈ bondSites (attachBonds (attachBondSet hd R x y) x x' y y'), z ∈ K.supp :=
    fun z hz => hK z (Or.inl (hreach.1 z hz))
  have hCK : ∀ z ∈ C.supp, z ∈ K.supp := fun z hz => hK z (Or.inr hz)
  by_contra hcon
  push Not at hcon
  set U : Vertex d → ℝ := Rigidity.Section3.extend K u with hU
  have hUK : ∀ z (hz : z ∈ K.supp), U z = u ⟨z, hz⟩ := fun z hz => by
    simp [hU, Rigidity.Section3.extend, hz]
  have hharm : ∀ z ∈ K.supp,
      Graph.laplacian (openGraph (attachedEnv hd R x x' y y' ω)) U z = 0 := by
    intro z hz
    rw [← componentLaplacian_restrict_eq K U ⟨z, hz⟩]
    have : (fun y : K => U y.val) = u := funext fun y => hUK y.val y.2
    rw [this]
    exact hu.1.1 ⟨z, hz⟩
  have hgad : ∀ z w, z - gadgetShift d R ∈ ambientSites hd (R : ℤ) →
      w - gadgetShift d R ∈ ambientSites hd (R : ℤ) → U z = U w := by
    intro z w hz hw
    calc U z = U (gadgetShift d R + (z - gadgetShift d R)) := by rw [add_sub_cancel]
      _ = u ⟨_, hgK _ hz⟩ := hUK _ _
      _ = u ⟨_, hgK _ hw⟩ := hcon _ hz _ hw _ _
      _ = U (gadgetShift d R + (w - gadgetShift d R)) := (hUK _ _).symm
      _ = U w := by rw [add_sub_cancel]
  -- the maximum principle on `P₁` and on `P₂`
  have hopen := attachBonds_open (hd := hd) (by omega : 4 ≤ R) hx hy ω
  have hxx' : (openGraph (attachedEnv hd R x x' y y' ω)).Adj x x' :=
    ⟨hx.2.2, hopen _ (Or.inr (Or.inl rfl))⟩
  have hyy' : (openGraph (attachedEnv hd R x x' y y' ω)).Adj y y' :=
    ⟨hy.2.2, hopen _ (Or.inr (Or.inr rfl))⟩
  have hfinP : ∀ P ⊆ attachBondSet hd R x y, (bondSites P).Finite := fun P hP =>
    (cube_finite d R).subset fun z ⟨e, he, hze⟩ =>
      attachBondSet_cube (by omega) hx hy e (hP he) z hze
  have hharmP : ∀ P ⊆ attachBondSet hd R x y, ∀ z ∈ bondSites P,
      Graph.laplacian (openGraph (attachedEnv hd R x x' y y' ω)) U z = 0 :=
    fun P hP z ⟨e, he, hze⟩ => hharm z (hFK z ⟨e, Or.inl (hP he), hze⟩)
  have hlowsub : lowPathBonds hd R x y ⊆ attachBondSet hd R x y := fun e he => Or.inl (Or.inr he)
  have hhighsub : highPathBonds hd R x y ⊆ attachBondSet hd R x y := fun e he => Or.inr he
  have hlowopen : ∀ f ∈ lowPathBonds hd R x y, (attachedEnv hd R x x' y y' ω) f = true :=
    fun f hf => hopen f (Or.inl (hlowsub hf))
  have hhighopen : ∀ f ∈ highPathBonds hd R x y, (attachedEnv hd R x x' y y' ω) f = true :=
    fun f hf => hopen f (Or.inl (hhighsub hf))
  obtain ⟨hlo, hs⟩ := lowPath_ends (hd := hd) hR hx hy
  obtain ⟨hhi, ht⟩ := highPath_ends (hd := hd) hR hx hy
  have hst : U (zeroPad d (-2, -halfSide R - 1)) = U (zeroPad d (1, -halfSide R - 1)) :=
    hgad _ _ (by rw [zeroPad_terminal_s, add_sub_cancel_left]; exact zeroPad_one_one_mem hd R)
      (by rw [zeroPad_terminal_t, add_sub_cancel_left]; exact zeroPad_four_one_mem hd R)
  have hvals : U x = U x' ∧ U y = U y' ∧ U x' = U y' := by
    rcases lowSite_highSite_cases (hd := hd) x y with ⟨hl, hh⟩ | ⟨hl, hh⟩
    · have h1 := path_value_eq (a' := x') (hfinP _ hlowsub) (by rw [hl]; exact hxx')
        (fun z hz => chainBonds_reach _ _ z hz) hlowopen (hharmP _ hlowsub)
        (fun z hz w hw => path_out hR hx hy hxy hgad (Or.inl ⟨rfl, rfl⟩)
          (Or.inl ⟨rfl, by rw [hh] at hhi; exact hhi⟩) hz hw)
      have h2 := path_value_eq (a' := y') (hfinP _ hhighsub) (by rw [hh]; exact hyy')
        (fun z hz => chainBonds_reach _ _ z hz) hhighopen (hharmP _ hhighsub)
        (fun z hz w hw => path_out hR hx hy hxy hgad (Or.inr ⟨rfl, rfl⟩)
          (Or.inr ⟨rfl, by rw [hl] at hlo; exact hlo⟩) hz hw)
      have e1 := h1 _ hlo
      have e2 := h2 _ hhi
      rw [hl] at e1
      rw [hh] at e2
      exact ⟨e1, e2, by rw [← h1 _ hs, ← h2 _ ht, hst]⟩
    · have h1 := path_value_eq (a' := y') (hfinP _ hlowsub) (by rw [hl]; exact hyy')
        (fun z hz => chainBonds_reach _ _ z hz) hlowopen (hharmP _ hlowsub)
        (fun z hz w hw => path_out hR hx hy hxy hgad (Or.inl ⟨rfl, rfl⟩)
          (Or.inr ⟨rfl, by rw [hh] at hhi; exact hhi⟩) hz hw)
      have h2 := path_value_eq (a' := x') (hfinP _ hhighsub) (by rw [hh]; exact hxx')
        (fun z hz => chainBonds_reach _ _ z hz) hhighopen (hharmP _ hhighsub)
        (fun z hz w hw => path_out hR hx hy hxy hgad (Or.inr ⟨rfl, rfl⟩)
          (Or.inl ⟨rfl, by rw [hl] at hlo; exact hlo⟩) hz hw)
      have e1 := h1 _ hlo
      have e2 := h2 _ hhi
      rw [hl] at e1
      rw [hh] at e2
      exact ⟨e2, e1, by rw [← h1 _ hs, ← h2 _ ht, hst]⟩
  obtain ⟨hvx, hvy, hvxy⟩ := hvals
  -- `ℓ'_q` is harmonic on `𝒞̃_∞`
  have hlapC : ∀ z ∈ C.supp, Graph.laplacian (openGraph (closedNear R ω)) U z = 0 := by
    intro z hz
    have hzR := not_mem_cube_of_infinite hCinf hz
    rw [laplacian_eq_of_adj (ω₂ := attachedEnv hd R x x' y y' ω) U z
      (fun w hw => (closedNear_adj hw).2) ?_]
    · exact hharm z (hCK z hz)
    intro w hw hnw
    rcases attachConfig_adj hw with h' | ⟨hab, hF⟩
    · exact absurd h' hnw
    rcases hF with hH | he | he
    · exact absurd (attachBondSet_cube (by omega) hx hy _ hH z (Sym2.mem_mk_left z w)) hzR
    · rcases Sym2.eq_iff.mp he with ⟨hzx, -⟩ | ⟨hzx, hwx⟩
      · exact absurd (hzx ▸ hx.1) hzR
      · rw [hzx, hwx, hvx]
    · rcases Sym2.eq_iff.mp he with ⟨hzy, -⟩ | ⟨hzy, hwy⟩
      · exact absurd (hzy ▸ hy.1) hzR
      · rw [hzy, hwy, hvy]
  -- `ℓ'_q - ℓ̃_q` is a sublinear harmonic function on `𝒞̃_∞`
  set v : C → ℝ := fun z => U z.val - ũ z with hv
  have hvlap : ∀ z, componentLaplacian C v z = 0 := by
    intro z
    calc componentLaplacian C v z =
        componentLaplacian C (fun y => U y.val) z - componentLaplacian C ũ z :=
          Rigidity.Steps.S3.componentLaplacian_sub C _ ũ z
      _ = 0 := by rw [componentLaplacian_restrict_eq C U z, hlapC z.val z.2, hũ.1.1 z, sub_zero]
  have hvslope : componentSlopeAsymptotics C 0 v := by
    intro ε hε
    obtain ⟨R₁, hR₁, h₁⟩ := hu.2 (ε / 2) (half_pos hε)
    obtain ⟨R₂, -, h₂⟩ := hũ.2 (ε / 2) (half_pos hε)
    refine ⟨max R₁ R₂, lt_max_of_lt_left hR₁, fun r hr z hz => ?_⟩
    have hzK := hCK z.val z.2
    have e1 := abs_le.mp (h₁ r (le_of_max_le_left hr) ⟨z.val, hzK⟩
      (by rw [mem_componentEuclideanBall] at hz ⊢; exact hz))
    have e2 := abs_le.mp (h₂ r (le_of_max_le_right hr) z hz)
    have hsl : componentSlope K q ⟨z.val, hzK⟩ = componentSlope C q z := rfl
    have h0 : componentSlope C 0 z = 0 := by simp [componentSlope]
    have hvz : v z = (u ⟨z.val, hzK⟩ - componentSlope C q z) - (ũ z - componentSlope C q z) := by
      simp only [hv, hUK _ hzK]
      ring
    rw [hsl] at e1
    rw [h0, sub_zero, hvz, abs_le]
    constructor <;> linarith [e1.1, e1.2, e2.1, e2.2]
  obtain ⟨c, hc⟩ := hliou v hvlap hvslope
  have e := (hc ⟨x', hx'⟩).trans (hc ⟨y', hy'⟩).symm
  simp only [hv] at e
  exact hne (by linarith)

end Attached

/-! ### `step:4.8-attach` -/

/-- **`step:4.8-attach`** (paper L1411-1415, Figure `attach-gadget`) for the construction
`H = attachBondSet`, `τ = gadgetShift` of `Rigidity/Proofs/S4/GadgetPlacement.lean`: almost
surely, for boundary placements `(x, x̃), (y, ỹ)` with `x ≠ y` separated by a corrected plane of
the closed environment, the attachment has `𝒞'_∞ ∩ Q_R = H` and a corrected plane of `𝒞'_∞` not
constant on the gadget. Cited inputs: `SupercriticalBondCorrectorInput` (corrected planes) and
`ArmstrongDarioOrderZero` (Theorem 2.4 at order zero). -/
theorem attachStep [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) (q : Fin d → ℝ)
    (corrector : LatticeProb.External.SupercriticalBondCorrectorInput)
    (orderZero : LatticeProb.External.ArmstrongDarioOrderZero) :
    AttachStep hd p q (attachBondSet hd) (gadgetShift d) := by
  have hp0 : 0 < (p : ℝ) := (criticalProbability_nonneg d).trans_lt hpc
  refine ⟨5, fun R hR => ?_⟩
  have hL := ae_attachConfig hp0 hp1 R ∅
    (Rigidity.Proofs.S3.sublinearLiouvilleStep hd p hpc hp1 orderZero)
  have hC : ∀ᵐ ω ∂latticeBondLaw d p, ∀ z : Vertex d × Vertex d × Vertex d × Vertex d,
      ∀ h' : HasUniqueInfiniteOpenComponent
        (attachedEnv hd R z.1 z.2.1 z.2.2.1 z.2.2.2 ω),
      ∀ (q : Fin d → ℝ) (o : uniqueInfiniteComponent h'),
        ∃! u : uniqueInfiniteComponent h' → ℝ,
          IsCorrectedPlane (uniqueInfiniteComponent h') q u ∧ u o = 0 := by
    rw [ae_all_iff]
    intro z
    filter_upwards [ae_attachConfig hp0 hp1 R
      (attachBonds (attachBondSet hd R z.1 z.2.2.1) z.1 z.2.1 z.2.2.1 z.2.2.2)
      (corrector d hd p hpc hp1)] with ω hω h'
    exact (hω h').1
  filter_upwards [hL, hC] with ω hLω hCω
  intro x x' y y' hx hy hxy hW
  obtain ⟨h, hx', hy', ũ, hũ, hne⟩ := hW
  rw [← closedNear_eq_attachConfig] at hLω
  obtain ⟨h', hx'K, hK⟩ := attached_unique (hd := hd) hR hx hy h hx'
  obtain ⟨u, ⟨hu, -⟩, -⟩ := hCω (x, x', y, y') h' q ⟨x', hx'K⟩
  have hreach := attached_reachable (hd := hd) hR hx hy ω
  refine ⟨⟨h', attached_componentBondsIn hR hx hy _ fun z hz => hK z (Or.inl (hreach.1 z ?_))⟩,
    h', u, hu, attached_gadget_nonconstant hR hx hy hxy _ (uniqueInfiniteComponent_infinite h)
      hx' hy' ũ hũ hne (hLω h) _ hK u hu⟩
  obtain ⟨e, he, hze⟩ := hz
  exact ⟨e, Or.inl he, hze⟩

end Rigidity.Proofs.S4
