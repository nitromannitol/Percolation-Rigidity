import Rigidity.Proofs.S4.OuterNonConstant.Envs

/-!
# Lemma 4.8, conditional form: compatibility of the reset and the comparison step

* `attach_compat`: after the attachment reset, on the gadget event, the bond set
  `H = 𝒞_∞ ∩ Q_R` contains the gadget as an induced subgraph and `A_H` fixes the reset bonds
  (the hypothesis of `exists_conditional_ge`).
* `compare_faces`: if the connector bonds of `ω` are open and a corrected plane of `ω` takes two
  values on `Q_{R-1}`, then the corrected plane of `ρ₀` is not constant on the face sites, which lie
  in its infinite cluster.
-/

namespace Rigidity.Proofs.S4.OuterNonConstant

open LatticeProb LatticeProb.Percolation LatticeProb.Network
  LatticeProb.Network.OpenLadder.Embedding Rigidity.Section4 Rigidity.Steps.S4
  Rigidity.Proofs.S4.Conditioning

open scoped Classical

variable {d : ℕ} {R : ℕ} {w : Vertex d}

theorem attachEnv_face (hd : 2 ≤ d) {ω : Configuration d} {e : Bond d}
    (he : e ∈ faceBonds d R) : attachEnv hd R w ω e = true := by
  rw [attachEnv_apply hd, if_pos (mem_attachResetBonds_of_faceBonds hd he), decide_eq_true_eq]
  exact Or.inl he

theorem attachEnv_conn (hd : 2 ≤ d) {ω : Configuration d} {e : Bond d}
    (he : e ∈ connectorBonds d R) : attachEnv hd R w ω e = true := by
  have he' : e ∈ attachResetBonds hd R w := Set.mem_union_right _ he
  rw [attachEnv_apply hd, if_pos he', decide_eq_true_eq]
  exact Or.inr (Or.inl he)

/-- The bond of two adjacent sites. -/
theorem mem_bondOfAdjacent_left {x y : Vertex d} (h : (nearestNeighborGraph d).Adj x y) :
    x ∈ ((bondOfAdjacent h : Bond d) : Sym2 (Vertex d)) := Sym2.mem_mk_left x y

theorem mem_bondOfAdjacent_right {x y : Vertex d} (h : (nearestNeighborGraph d).Adj x y) :
    y ∈ ((bondOfAdjacent h : Bond d) : Sym2 (Vertex d)) := Sym2.mem_mk_right x y

theorem cube_pred_subset : cube d (R - 1) ⊆ cube d R := fun _ hx i =>
  (hx i).trans (by exact_mod_cast Nat.sub_le R 1)

theorem mem_cube_of_mem_coreBonds {e : Bond d} (he : e ∈ coreBonds d R) :
    ∀ z ∈ (e : Sym2 (Vertex d)), z ∈ cube d R := fun z hz =>
  (he z hz).elim mem_cube_of_mem_faceSites fun h => cube_pred_subset h

/-- **Compatibility of the attachment reset** (hypothesis of `exists_conditional_ge`). -/
theorem attach_compat (hd : 2 ≤ d) (hR : 10 ≤ R) (hw : w ∈ faceSites d R)
    (hw0 : w ≠ refSite d R) {q : Fin d → ℝ} (ω : Configuration d)
    (hG : attachEnv hd R w ω ∈ gadgetNonconstantEvent hd q R (gadgetShift d R)) :
    ∃ H, IsGadgetPlacement hd R H (gadgetShift d R) ∧
      attachEnv hd R w ω ∈ conditioningEvent d R H ∧
      conditioningEvent d R H ⊆ resetEvent (attachResetBonds hd R w) (attachPattern hd R w) := by
  obtain ⟨h, -, -, g, hg, -, -, hgK, -, -⟩ := hG
  set K := uniqueInfiniteComponent h with hKdef
  have hR1 : 1 ≤ R := by omega
  have hz₀ := refSite_mem hd hR
  have hgadopen : ∀ f ∈ gadgetBonds hd R, attachEnv hd R w ω f = true :=
    fun f hf => attachEnv_branch hd hR hw hw0 (Or.inl (Or.inl (Or.inl hf)))
  -- the branch, the faces and the connectors lie in the cluster
  have hsK : zeroPad d (-2, -halfSide R - 1) ∈ K.supp := by
    have h1 := gadget_reachable_of_open hd (by omega) hgadopen hg (zeroPad_s_mem hd R)
    rw [add_sub_cancel] at h1
    exact mem_supp_of_reachable K hgK h1
  have hgadK : ∀ g' ∈ ambientSites hd (R : ℤ), gadgetShift d R + g' ∈ K.supp := fun g' hg' =>
    mem_supp_of_reachable K hgK (gadget_reachable_of_open hd (by omega) hgadopen hg hg')
  have hlowopen : ∀ f ∈ chainBonds (lowWaypoints hd R w), attachEnv hd R w ω f = true :=
    fun f hf => attachEnv_branch hd hR hw hw0 (Or.inl (Or.inl (Or.inr hf)))
  have hhighopen : ∀ f ∈ chainBonds (highWaypoints d R), attachEnv hd R w ω f = true :=
    fun f hf => attachEnv_branch hd hR hw hw0 (Or.inl (Or.inr hf))
  have hw1K : innerNeighbor R w ∈ K.supp := by
    obtain ⟨W, hW⟩ := chainBonds_reach (innerNeighbor R w) (lowWaypoints hd R w).tail _
      (lowBranch_ends hd hR hw).2
    exact mem_supp_of_reachable K hsK (openGraph_reachable_of_walk hlowopen W hW).symm
  have hlowK : ∀ z ∈ bondSites (chainBonds (lowWaypoints hd R w)), z ∈ K.supp := by
    intro z hz
    obtain ⟨W, hW⟩ := chainBonds_reach (innerNeighbor R w) (lowWaypoints hd R w).tail z hz
    exact mem_supp_of_reachable K hw1K (openGraph_reachable_of_walk hlowopen W hW)
  have hwK : w ∈ K.supp := by
    refine mem_supp_of_reachable K hw1K (SimpleGraph.Adj.reachable ?_)
    refine ⟨(adj_innerNeighbor hR1 hw).symm, attachEnv_branch hd hR hw hw0 (Or.inr (Or.inl ?_))⟩
    exact Sym2.eq_swap
  have hfaceK : ∀ a ∈ faceSites d R, a ∈ K.supp := fun a ha =>
    mem_supp_of_reachable K hwK (reachable_of_faceSites hd (by omega)
      (fun e he => attachEnv_face hd he) (fun e he => attachEnv_conn hd he) hw ha)
  have hz1K : zeroPad d (1, -((R : ℤ) - 1)) ∈ K.supp := by
    refine mem_supp_of_reachable K (hfaceK _ hz₀) (SimpleGraph.Adj.reachable ?_)
    rw [← innerNeighbor_refSite (by omega)]
    refine ⟨adj_innerNeighbor hR1 hz₀, attachEnv_branch hd hR hw hw0 (Or.inr (Or.inr rfl))⟩
  have hhighK : ∀ z ∈ bondSites (chainBonds (highWaypoints d R)), z ∈ K.supp := by
    intro z hz
    obtain ⟨W, hW⟩ := chainBonds_reach _ _ z hz
    exact mem_supp_of_reachable K hz1K (openGraph_reachable_of_walk hhighopen W hW)
  have hVal : ∀ e : Bond d, attachPattern hd R w e = true → ∀ z ∈ (e : Sym2 (Vertex d)),
      z ∈ K.supp := by
    intro e he z hz
    simp only [attachPattern, decide_eq_true_eq] at he
    rcases he with hf | hk | ((hg' | hl) | hh) | ha
    · exact hfaceK z (hf z hz)
    · by_cases hzf : z ∈ faceSites d R
      · exact hfaceK z hzf
      obtain ⟨a, ha, haf⟩ := exists_faceSite_of_mem_connectorBonds (by omega) hk
      obtain ⟨y, hay, he'⟩ := exists_adj_of_mem ha
      have hzy : z = y := by
        rw [he', Sym2.mem_iff] at hz
        rcases hz with rfl | rfl
        · exact absurd haf hzf
        · rfl
      subst hzy
      refine mem_supp_of_reachable K (hfaceK a haf) (SimpleGraph.Adj.reachable ⟨hay, ?_⟩)
      have : bondOfAdjacent hay = e := Subtype.ext he'.symm
      rw [this]
      exact attachEnv_conn hd hk
    · have := hgadK _ (hg' z hz)
      rwa [add_sub_cancel] at this
    · exact hlowK z ⟨e, hl, hz⟩
    · exact hhighK z ⟨e, hh, hz⟩
    · rcases ha with ha | ha <;> rw [ha, Sym2.mem_iff] at hz <;> rcases hz with rfl | rfl
      · exact hwK
      · exact hw1K
      · exact hfaceK _ hz₀
      · rw [innerNeighbor_refSite (by omega)]; exact hz1K
  have hDcube : ∀ e ∈ attachResetBonds hd R w, ∀ z ∈ (e : Sym2 (Vertex d)), z ∈ cube d R := by
    rintro e (⟨hc, -⟩ | hk) z hz
    · exact mem_cube_of_mem_coreBonds hc z hz
    · exact mem_cube_of_mem_connectorBonds (by omega) hk z hz
  have hpatt : ∀ e, attachPattern hd R w e = true → (∀ z ∈ (e : Sym2 (Vertex d)), z ∈ cube d R) →
      e ∈ componentBondsIn K (cube d R) := by
    intro e he hcube
    have heD : attachEnv hd R w ω e = true := by
      simp only [attachPattern, decide_eq_true_eq] at he
      rcases he with hf | hk | hb
      · exact attachEnv_face hd hf
      · exact attachEnv_conn hd hk
      · exact attachEnv_branch hd hR hw hw0 hb
    exact ⟨heD, fun z hz => ⟨hcube z hz, hVal e he z hz⟩⟩
  refine ⟨componentBondsIn K (cube d R), ⟨fun e he z hz => (he.2 z hz).1,
    fun x hx => gadget_mem_cube hd (by omega) hx, fun x hx y hy hxy => ⟨fun _ => ?_, fun _ => ?_⟩⟩,
    ⟨h, rfl⟩, ?_⟩
  · rw [ambientGraph, SimpleGraph.induce_adj]
    rw [add_comm (gadgetShift d R) x, add_comm (gadgetShift d R) y] at hxy
    exact (nearestNeighborGraph_adj_add_iff x y _).mp hxy
  · have hgb : bondOfAdjacent hxy ∈ gadgetBonds hd R := by
      intro z hz
      simp only [bondOfAdjacent, Sym2.mem_iff] at hz
      rcases hz with rfl | rfl
      · simpa using hx
      · simpa using hy
    refine hpatt _ (by simp [attachPattern, branchBonds, hgb]) fun z hz => ?_
    have := gadget_mem_cube hd (by omega) (hgb z hz)
    rwa [add_sub_cancel] at this
  · intro ω'' hω'' e he
    have hpe := conditioningEvent_subset_patternEvent R (componentBondsIn K (cube d R)) hω''
    have hsite : ∃ z ∈ (e : Sym2 (Vertex d)),
        z ∈ siteSet (componentBondsIn K (cube d R)) := by
      have hface_site : ∀ z ∈ faceSites d R, z ∈ siteSet (componentBondsIn K (cube d R)) := by
        intro z hz
        obtain ⟨y, hy, hzy⟩ := exists_adj_faceSites hd (by omega) hz
        have hfb : bondOfAdjacent hzy ∈ faceBonds d R := by
          intro u hu
          simp only [bondOfAdjacent, Sym2.mem_iff] at hu
          rcases hu with rfl | rfl
          · exact hz
          · exact hy
        exact ⟨_, hpatt _ (by simp [attachPattern, hfb]) fun u hu =>
          mem_cube_of_mem_faceSites (hfb u hu), mem_bondOfAdjacent_left hzy⟩
      rcases he with ⟨-, z, hz, hzf | ⟨f, hf, hzf⟩⟩ | hk
      · exact ⟨z, hz, hface_site z hzf⟩
      · exact ⟨z, hz, f, hpatt f (by simp [attachPattern, hf])
          (mem_cube_of_mem_coreBonds (branchBonds_core hd hR hw hw0 hf)), hzf⟩
      · obtain ⟨z, hz, hzf⟩ := exists_faceSite_of_mem_connectorBonds (by omega) hk
        exact ⟨z, hz, hface_site z hzf⟩
    rw [hpe e ⟨hDcube e he, hsite⟩]
    by_cases hp : attachPattern hd R w e = true
    · rw [hp, decide_eq_true_eq]
      exact hpatt e hp (hDcube e he)
    · rw [Bool.not_eq_true] at hp
      rw [hp, decide_eq_false_iff_not]
      intro hmem
      have h1 := hmem.1
      rw [attachEnv, resetConfig_of_mem he, hp] at h1
      exact absurd h1 (by simp)

/-! ### The comparison step -/

theorem compareEnv_face {ω : Configuration d} {e : Bond d} (he : e ∈ faceBonds d R) :
    compareEnv d R ω e = true := by
  rw [compareEnv_apply, if_pos (Set.mem_union_left _ (faceBonds_subset_coreBonds he)),
    decide_eq_true_eq]
  exact Or.inl he

theorem compareEnv_conn {ω : Configuration d} {e : Bond d} (he : e ∈ connectorBonds d R) :
    compareEnv d R ω e = true := by
  rw [compareEnv_apply, if_pos (Set.mem_union_right _ he), decide_eq_true_eq]
  exact Or.inr he

/-- Off `Q_{R-1}` and the face sites, the open bonds of `ω` are open in `ρ₀`. -/
theorem compareEnv_adj_of_adj {ω : Configuration d} {z y : Vertex d}
    (hz : z ∉ faceSites d R) (hzc : z ∉ cube d (R - 1)) (h : (openGraph ω).Adj z y) :
    (openGraph (compareEnv d R ω)).Adj z y := by
  obtain ⟨hzy, ho⟩ := h
  refine ⟨hzy, ?_⟩
  rw [compareEnv_apply]
  split_ifs with hD
  · rcases hD with hc | hk
    · rcases hc z (mem_bondOfAdjacent_left hzy) with h' | h'
      · exact absurd h' hz
      · exact absurd h' hzc
    · rw [decide_eq_true_eq]; exact Or.inr hk
  · exact ho

/-- The sites of `𝒞_∞(ω)` outside `𝒞_∞(ρ₀)` are finitely many. -/
theorem finite_supp_diff_compare (hR : 2 ≤ R) {ω : Configuration d}
    (C : OpenComponent ω) (hCinf : C.supp.Infinite) (C₀ : OpenComponent (compareEnv d R ω))
    (huniq : ∀ D : OpenComponent (compareEnv d R ω), D.supp.Infinite → D = C₀) :
    (C.supp \ C₀.supp).Finite := by
  let G₀ := openGraph (compareEnv d R ω)
  let S : Vertex d → Set (Vertex d) := fun a => {z | a ∉ C₀.supp ∧ z ∈ (G₀.connectedComponentMk a).supp}
  have hS : ∀ a, (S a).Finite := by
    intro a
    by_cases ha : a ∈ C₀.supp
    · exact Set.finite_empty.subset fun z hz => absurd ha hz.1
    · refine Set.Finite.subset ?_ fun z hz => hz.2
      by_contra hinf
      exact ha (huniq _ hinf ▸ (SimpleGraph.ConnectedComponent.mem_supp_iff _ a).mpr rfl)
  refine ((cube_finite d (R - 1)).union
    ((finite_faceSites (d := d) (R := R)).biUnion fun a _ => hS a)).subset ?_
  rintro z ⟨hzC, hzC₀⟩
  by_cases hzc : z ∈ cube d (R - 1)
  · exact Or.inl hzc
  right
  by_contra hno
  simp only [Set.mem_iUnion, not_exists] at hno
  have hnoreach : ∀ a ∈ faceSites d R, ¬ G₀.Reachable z a := by
    intro a ha hza
    have hzK : z ∈ (G₀.connectedComponentMk a).supp :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff _ z).mpr
        (SimpleGraph.ConnectedComponent.sound hza)
    by_cases haC : a ∈ C₀.supp
    · apply hzC₀
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at haC ⊢
      rw [← haC]; exact SimpleGraph.ConnectedComponent.sound hza
    · exact hno a ha ⟨haC, hzK⟩
  have key : ∀ x y (W : (openGraph ω).Walk x y), G₀.Reachable z x → x ∉ faceSites d R →
      x ∉ cube d (R - 1) → G₀.Reachable z y := by
    intro x y W
    induction W with
    | nil => exact fun hx _ _ => hx
    | @cons a b c hab W ih =>
      intro hza haf hac
      have h1 : G₀.Adj a b := compareEnv_adj_of_adj haf hac hab
      have hzb : G₀.Reachable z b := hza.trans h1.reachable
      have hbf : b ∉ faceSites d R := fun hb => hnoreach b hb hzb
      have hbc : b ∉ cube d (R - 1) := fun hb =>
        (mem_cube_pred_or_faceSites_of_adj (by omega) hb hab.1.symm).elim hac haf
      exact ih hzb hbf hbc
  have hzf : z ∉ faceSites d R := fun hz => hnoreach z hz SimpleGraph.Reachable.rfl
  have hsub : C.supp ⊆ (G₀.connectedComponentMk z).supp := by
    intro y hy
    have hzy : (openGraph ω).Reachable z y := by
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hzC hy
      exact SimpleGraph.ConnectedComponent.exact (hzC.trans hy.symm)
    obtain ⟨W⟩ := hzy
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ y).mpr
      (SimpleGraph.ConnectedComponent.sound (key z y W SimpleGraph.Reachable.rfl hzf hzc).symm)
  have hK' := huniq _ (Set.Infinite.mono hsub hCinf)
  exact hzC₀ (hK' ▸ (SimpleGraph.ConnectedComponent.mem_supp_iff _ z).mpr rfl)

/-- **The comparison step.** If the connector bonds of `ω` are open, the Liouville theorem holds on
`𝒞_∞(ω)`, and a corrected plane `ℓ` of `ω` takes two values on `Q_{R-1}`, then the face sites lie
in the infinite cluster `𝒞₀` of `ρ₀` and a corrected plane `ℓ₀` of `ρ₀` separates a face site
`w ≠ z₀` from `z₀`. -/
theorem compare_faces (hd : 2 ≤ d) (hR : 10 ≤ R) {q : Fin d → ℝ} {ω : Configuration d}
    (hK : ∀ e ∈ connectorBonds d R, ω e = true) (C : OpenComponent ω) (hCinf : C.supp.Infinite)
    (hliou : ∀ v : C → ℝ, (∀ x, componentLaplacian C v x = 0) →
      componentSlopeAsymptotics C 0 v → ∃ c : ℝ, ∀ x, v x = c)
    (ℓ : C → ℝ) (hℓ : IsCorrectedPlane C q ℓ)
    (htwo : ∃ x y : C, x.1 ∈ cube d (R - 1) ∧ y.1 ∈ cube d (R - 1) ∧ ℓ x ≠ ℓ y)
    (C₀ : OpenComponent (compareEnv d R ω)) (hC₀inf : C₀.supp.Infinite)
    (huniq : ∀ D : OpenComponent (compareEnv d R ω), D.supp.Infinite → D = C₀)
    (ℓ₀ : C₀ → ℝ) (hℓ₀ : IsCorrectedPlane C₀ q ℓ₀) :
    ∃ hface : faceSites d R ⊆ C₀.supp, ∃ w, ∃ hw : w ∈ faceSites d R, w ≠ refSite d R ∧
      ℓ₀ ⟨w, hface hw⟩ ≠ ℓ₀ ⟨refSite d R, hface (refSite_mem hd hR)⟩ := by
  -- `ℓ₀` is not constant on the face sites of `𝒞₀`
  have hnc : ¬ ∃ c : ℝ, ∀ a ∈ faceSites d R, ∀ ha : a ∈ C₀.supp, ℓ₀ ⟨a, ha⟩ = c := by
    rintro ⟨c, hc⟩
    have hdiff : ∀ z y, Xor ((openGraph ω).Adj z y) ((openGraph (compareEnv d R ω)).Adj z y) →
        ∀ hz : z ∈ C₀.supp, ℓ₀ ⟨z, hz⟩ = c := by
      intro z y hxor hz
      have hzc : z ∉ cube d (R - 1) := fun h' =>
        not_mem_supp_compareEnv (by omega) C₀ hC₀inf h' hz
      by_cases hzf : z ∈ faceSites d R
      · exact hc z hzf hz
      exfalso
      rcases hxor with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact h2 (compareEnv_adj_of_adj hzf hzc h1)
      · obtain ⟨hzy, ho⟩ := h1
        apply h2
        refine ⟨hzy, ?_⟩
        rw [compareEnv_apply] at ho
        split_ifs at ho with hD
        · rcases hD with hcore | hk
          · rcases hcore z (mem_bondOfAdjacent_left hzy) with h' | h'
            · exact absurd h' hzf
            · exact absurd h' hzc
          · exact hK _ hk
        · exact ho
    obtain ⟨k, hk⟩ := exists_const_of_compare C C₀ hliou hℓ hℓ₀ c hdiff
      (finite_supp_diff_compare (by omega) C hCinf C₀ huniq)
    obtain ⟨x, y, hx, hy, hxy⟩ := htwo
    have hxC : ∀ hx' : x.1 ∈ C₀.supp, ℓ₀ ⟨x.1, hx'⟩ = c := fun hx' =>
      absurd hx' (not_mem_supp_compareEnv (by omega) C₀ hC₀inf hx)
    have hyC : ∀ hy' : y.1 ∈ C₀.supp, ℓ₀ ⟨y.1, hy'⟩ = c := fun hy' =>
      absurd hy' (not_mem_supp_compareEnv (by omega) C₀ hC₀inf hy)
    exact hxy ((hk x hxC).trans (hk y hyC).symm)
  -- a face site of `𝒞₀`, and the face sites lie in `𝒞₀`
  obtain ⟨a₀, ha₀, ha₀C⟩ : ∃ a ∈ faceSites d R, a ∈ C₀.supp := by
    by_contra hno
    push Not at hno
    exact hnc ⟨0, fun a ha haC => absurd haC (hno a ha)⟩
  have hface : faceSites d R ⊆ C₀.supp := fun a ha =>
    mem_supp_of_reachable C₀ ha₀C (reachable_of_faceSites hd (by omega)
      (fun e he => compareEnv_face he) (fun e he => compareEnv_conn he) ha₀ ha)
  refine ⟨hface, ?_⟩
  have hz₀ := refSite_mem hd hR
  by_contra hall
  push Not at hall
  apply hnc
  refine ⟨ℓ₀ ⟨refSite d R, hface hz₀⟩, fun a ha haC => ?_⟩
  by_cases haz : a = refSite d R
  · subst haz; rfl
  · exact hall a ha haz

end Rigidity.Proofs.S4.OuterNonConstant
