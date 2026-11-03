import Rigidity.Steps.S4.NonConstantOnGadgetJoint
import Rigidity.Proofs.S3.FiniteEnergy
import Rigidity.Proofs.S3.FlipCorrector
import Rigidity.Proofs.S3.SublinearLiouville
import Rigidity.Proofs.S3.Divergence

/-!
# Lemma 4.8: the corrected plane after closing the bonds meeting `Q_R`

Step `step:4.8-closed-boundary` (`Rigidity.Steps.S4.ClosedBoundaryStep`, paper L1406-1411 of the
corrected draft). Let `ω` lie in the event `E_R`, `𝒞_∞` its infinite cluster, `ℓ_q` a corrected
plane of `𝒞_∞` with slope `q ≠ 0`, and `𝒞̃_∞` the infinite cluster of the environment `ω̃` in which
every bond meeting `Q_R` is closed, with corrected plane `ℓ̃_q`.

* `𝒞̃_∞ ⊆ 𝒞_∞`, `𝒞̃_∞` misses `Q_R` (its sites are isolated in `ω̃`), and `F = 𝒞_∞ \ 𝒞̃_∞` is
  finite: every cluster of `ω̃` inside `F` contains a site of `Q_{R+1}` and is finite.
* A boundary edge is an open edge `z w` of `ω` with `z ∈ 𝒞̃_∞` and `w ∈ F`; then `w ∈ Q_R`,
  `z ∉ Q_R`, so `(w, z)` is a boundary placement.
* If `ℓ̃_q` takes a single value `c` on the sites `z` of the boundary edges, then `ℓ̃_q` extended by
  `c` on `F` is harmonic on `𝒞_∞`, and `ℓ_q` minus it is harmonic and sublinear, hence constant by
  the Liouville theorem at order zero (`Rigidity.Proofs.S3.sublinearLiouvilleStep`).
* If two boundary edges `z₁ w₁`, `z₂ w₂` have `ℓ̃_q(z₁) ≠ ℓ̃_q(z₂)` but every such pair has
  `w₁ = w₂`, all boundary edges pass through a single site `x₀`, and the maximum principle on the
  finite set `F` (whose only exit is `x₀`) makes `ℓ_q` constant on `F`.

In both cases `ℓ_q` is constant on `Q_R ∩ 𝒞_∞ ⊆ F`, against `E_R` (`ℓ_q ∈ 𝒜₁(𝒞_∞)` is not constant
since `q ≠ 0`, by uniqueness of the slope). Hence two boundary edges `z₁ w₁`, `z₂ w₂` have
`w₁ ≠ w₂` and `ℓ̃_q(z₁) ≠ ℓ̃_q(z₂)`.

The paper chooses `x̃, ỹ` on opposite faces of `Q_{R+1}`; the step only needs `x ≠ y`, and the
second case above (which the printed argument does not address) is where `x ≠ y` is used. The
paper's claim that every face of `Q_{R+1}` meets `𝒞̃_∞` is not needed.

Cited inputs: `LatticeProb.External.ArmstrongDarioOrderZero` (uniqueness of the infinite cluster
and the Liouville theorem at order zero) and `LatticeProb.External.SupercriticalBondCorrectorInput`
(corrected planes of `ω` and of `ω̃`, uniqueness of the slope), transferred to `ω̃` by Lemma 2.1
(`Rigidity.Proofs.S3.ae_forall_closeBonds`, `Rigidity.Proofs.S3.flipCorrectorStep`).
-/

namespace Rigidity.Proofs.S4

open MeasureTheory LatticeProb.Percolation Rigidity.Section4 Rigidity.Steps.S4
open Rigidity.Proofs.S3 (componentLaplacian_eq_sum_lattice ae_forall_closeBonds flipCorrectorStep
  sublinearLiouvilleStep)
open scoped Classical

variable {d : ℕ}

theorem extend_of_mem {ω : Configuration d} {C : OpenComponent ω} {u : C → ℝ} {x : Vertex d}
    (hx : x ∈ C.supp) : Section3.extend C u x = u ⟨x, hx⟩ := dif_pos hx

theorem extend_of_not_mem {ω : Configuration d} {C : OpenComponent ω} {u : C → ℝ} {x : Vertex d}
    (hx : x ∉ C.supp) : Section3.extend C u x = 0 := dif_neg hx

/-- The cube `Q_R` is finite. -/
theorem finite_cube (d R : ℕ) : (cube d R).Finite :=
  (Set.finite_Icc (fun _ => -(R : ℤ)) (fun _ => (R : ℤ))).subset fun _ hy =>
    ⟨fun i => (abs_le.mp (hy i)).1, fun i => (abs_le.mp (hy i)).2⟩

/-- A lattice neighbour of a site of `Q_R` lies in `Q_{R+1}`. -/
theorem mem_cube_succ_of_adj {R : ℕ} {a b : Vertex d} (hab : (nearestNeighborGraph d).Adj a b)
    (hb : b ∈ cube d R) : a ∈ cube d (R + 1) := by
  have hsum := lattice_adj_iff_l1Dist.mp hab
  show ∀ i, |a i| ≤ ((R + 1 : ℕ) : ℤ)
  intro i
  have hi : |a i - b i| ≤ 1 :=
    hsum ▸ Finset.single_le_sum (f := fun j => |a j - b j|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ i)
  have hbi : |b i| ≤ (R : ℤ) := hb i
  rw [abs_le] at hi hbi ⊢
  push_cast
  constructor <;> linarith

/-- The bond of two adjacent sites meets `Q_R` iff one of them lies in `Q_R`. -/
theorem bondOfAdjacent_mem_bondsNear {R : ℕ} {a b : Vertex d}
    (hab : (nearestNeighborGraph d).Adj a b) :
    bondOfAdjacent hab ∈ bondsNear d R ↔ a ∈ cube d R ∨ b ∈ cube d R := by
  constructor
  · rintro ⟨z, hz, hzR⟩
    rcases Sym2.mem_iff.mp hz with rfl | rfl
    · exact Or.inl hzR
    · exact Or.inr hzR
  · rintro (h | h)
    · exact ⟨a, Sym2.mem_mk_left a b, h⟩
    · exact ⟨b, Sym2.mem_mk_right a b, h⟩

/-- The open edges of `ω̃` (the bonds meeting `Q_R` closed) are the open edges of `ω` away from
`Q_R`. -/
theorem closedNear_adj_iff {R : ℕ} {ω : Configuration d} {a b : Vertex d} :
    (openGraph (closedNear R ω)).Adj a b ↔
      (openGraph ω).Adj a b ∧ a ∉ cube d R ∧ b ∉ cube d R := by
  simp only [openGraph_adj_iff, closedNear]
  constructor
  · rintro ⟨hab, he⟩
    by_cases hmem : bondOfAdjacent hab ∈ bondsNear d R
    · rw [if_pos hmem] at he
      exact absurd he Bool.false_ne_true
    · rw [if_neg hmem] at he
      rw [bondOfAdjacent_mem_bondsNear, not_or] at hmem
      exact ⟨⟨hab, he⟩, hmem⟩
  · rintro ⟨⟨hab, he⟩, ha, hb⟩
    refine ⟨hab, ?_⟩
    rw [if_neg ((bondOfAdjacent_mem_bondsNear hab).not.mpr (not_or.mpr ⟨ha, hb⟩))]
    exact he

/-- An infinite cluster of `ω̃` misses `Q_R`: the sites of `Q_R` are isolated in `ω̃`. -/
theorem not_mem_cube_of_mem_supp {R : ℕ} {ω : Configuration d}
    (D : OpenComponent (closedNear R ω)) (hD : D.supp.Infinite) {x : Vertex d}
    (hx : x ∈ D.supp) : x ∉ cube d R := by
  intro hxR
  apply hD
  refine (Set.finite_singleton x).subset fun y hy => ?_
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hx hy
  obtain ⟨W⟩ := SimpleGraph.ConnectedComponent.exact (hx.trans hy.symm)
  cases W with
  | nil => exact Set.mem_singleton _
  | cons hadj _ => exact absurd hxR (closedNear_adj_iff.mp hadj).2.1

/-- A cluster of `ω̃` lies in the cluster of `ω` of any of its sites. -/
theorem supp_subset_of_closedNear {R : ℕ} {ω : Configuration d}
    (D : OpenComponent (closedNear R ω)) {v : Vertex d} (hv : v ∈ D.supp) :
    D.supp ⊆ ((openGraph ω).connectedComponentMk v).supp := by
  intro u hu
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hu hv ⊢
  exact SimpleGraph.ConnectedComponent.sound
    (SimpleGraph.Reachable.mono (fun _ _ h => (closedNear_adj_iff.mp h).1)
      (SimpleGraph.ConnectedComponent.exact (hu.trans hv.symm)))

/-- `F = 𝒞_∞ \ 𝒞̃_∞` is finite: the cluster of `ω̃` of a site of `F` is not `𝒞̃_∞`, hence finite,
and it contains a site of `Q_{R+1}` (the start of the first bond meeting `Q_R` on an open path of
`ω` to `𝒞̃_∞`). -/
theorem finite_supp_diff {R : ℕ} {ω : Configuration d} (C : OpenComponent ω)
    (C' : OpenComponent (closedNear R ω)) (hC' : C'.supp.Infinite)
    (huniq : ∀ D : OpenComponent (closedNear R ω), D.supp.Infinite → D = C')
    (hsub : C'.supp ⊆ C.supp) : (C.supp \ C'.supp).Finite := by
  obtain ⟨c, hc⟩ := hC'.nonempty
  refine ((finite_cube d (R + 1)).biUnion (t := fun a =>
    ((openGraph (closedNear R ω)).connectedComponentMk a).supp \ C'.supp) fun a _ => ?_).subset ?_
  · by_cases hD : ((openGraph (closedNear R ω)).connectedComponentMk a).supp.Infinite
    · rw [huniq _ hD, Set.sdiff_self]
      exact Set.finite_empty
    · exact (Set.not_infinite.mp hD).subset Set.sdiff_subset
  · rintro z ⟨hzC, hzC'⟩
    have hcC := hsub hc
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hzC hcC
    obtain ⟨W⟩ := SimpleGraph.ConnectedComponent.exact (hzC.trans hcC.symm)
    set K := (openGraph (closedNear R ω)).connectedComponentMk z with hK
    have hzK : z ∈ K.supp := rfl
    have hcK : c ∉ K.supp := by
      intro hcK
      apply hzC'
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hcK hc
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff, ← hc, hcK]
    obtain ⟨dt, -, hd1, hd2⟩ := W.exists_boundary_dart K.supp hzK hcK
    have hnot : ¬ (openGraph (closedNear R ω)).Adj dt.fst dt.snd :=
      fun h => hd2 (K.mem_supp_of_adj_mem_supp hd1 h)
    have hfst : dt.fst ∈ cube d (R + 1) := by
      by_cases hf : dt.fst ∈ cube d R
      · exact (fun i => (hf i).trans (by push_cast; omega) : ∀ i, |dt.fst i| ≤ ((R + 1 : ℕ) : ℤ))
      · have hs : dt.snd ∈ cube d R := by
          by_contra hs
          exact hnot (closedNear_adj_iff.mpr ⟨dt.adj, hf, hs⟩)
        exact mem_cube_succ_of_adj (openGraph_le ω dt.adj) hs
    refine Set.mem_iUnion₂.mpr ⟨dt.fst, hfst, ?_, hzC'⟩
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hd1 ⊢
    exact hd1.symm

/-- A boundary edge `z w` (`z ∈ 𝒞̃_∞`, `w ∉ 𝒞̃_∞`, open in `ω`) gives the boundary placement
`(w, z)`. -/
theorem mem_boundaryPairs_of_adj {R : ℕ} {ω : Configuration d}
    (C' : OpenComponent (closedNear R ω)) (hC' : C'.supp.Infinite) {z w : Vertex d}
    (hz : z ∈ C'.supp) (hw : w ∉ C'.supp) (hzw : (openGraph ω).Adj z w) :
    (w, z) ∈ boundaryPairs d R := by
  have hzR := not_mem_cube_of_mem_supp C' hC' hz
  have hwR : w ∈ cube d R := by
    by_contra hwR
    exact hw (C'.mem_supp_of_adj_mem_supp hz (closedNear_adj_iff.mpr ⟨hzw, hzR, hwR⟩))
  exact ⟨hwR, hzR, (openGraph_le ω hzw).symm⟩

/-- The Laplacian of `-u`. -/
theorem componentLaplacian_neg' {ω : Configuration d} (C : OpenComponent ω) (u : C → ℝ)
    (x : C) : componentLaplacian C (fun y => -u y) x = -componentLaplacian C u x := by
  simp only [componentLaplacian, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- Maximum principle with a single exit: let `T ⊆ 𝒞` be such that every open edge from `T` to
`𝒞 \ T` ends at `x₀`. If a harmonic `u` attains its maximum over `𝒞 \ T` at `z`, it also attains
it at `x₀`. -/
theorem extend_eq_of_isMaxOn {ω : Configuration d} (C : OpenComponent ω) {T : Set (Vertex d)}
    {t : Vertex d} (ht : t ∈ T) (hT : T ⊆ C.supp) {x₀ : Vertex d}
    (hall : ∀ z w, z ∈ T → w ∉ T → (openGraph ω).Adj z w → w = x₀) {u : C → ℝ}
    (hu : ∀ x, componentLaplacian C u x = 0) {z : Vertex d} (hz : z ∈ C.supp) (hzT : z ∉ T)
    (hmax : ∀ y ∈ C.supp, y ∉ T → Section3.extend C u y ≤ Section3.extend C u z) :
    Section3.extend C u x₀ = Section3.extend C u z := by
  by_cases hzx : z = x₀
  · rw [hzx]
  have htC := hT ht
  have hzC := hz
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hz htC
  obtain ⟨W⟩ := SimpleGraph.ConnectedComponent.exact (hz.trans htC.symm)
  let S : Set (Vertex d) :=
    {y | y ∈ C.supp ∧ y ∉ T ∧ y ≠ x₀ ∧ Section3.extend C u y = Section3.extend C u z}
  obtain ⟨dt, -, ⟨haC, haT, hax, hau⟩, hb⟩ :=
    W.exists_boundary_dart S ⟨hzC, hzT, hzx, rfl⟩ fun h => h.2.1 ht
  have hbC : dt.snd ∈ C.supp := C.mem_supp_of_adj_mem_supp haC dt.adj
  -- every open neighbour of `a` lies in `𝒞 \ T`
  have hnbr : ∀ y, (openGraph ω).Adj dt.fst y → y ∈ C.supp ∧ y ∉ T := fun y hy =>
    ⟨C.mem_supp_of_adj_mem_supp haC hy, fun hyT => hax (hall y dt.fst hyT haT hy.symm)⟩
  have hL := hu ⟨dt.fst, haC⟩
  rw [componentLaplacian_eq_sum_lattice C u dt.fst haC] at hL
  have hle : ∀ y ∈ (LatticeProb.lattice d).neighborFinset dt.fst,
      (if (openGraph ω).Adj dt.fst y then Section3.extend C u y - Section3.extend C u dt.fst else 0) ≤ 0 := by
    intro y _
    split_ifs with hy
    · have := hmax y (hnbr y hy).1 (hnbr y hy).2
      linarith
    · exact le_refl 0
  have hterm := (Finset.sum_eq_zero_iff_of_nonpos hle).mp hL dt.snd
    (by rw [SimpleGraph.mem_neighborFinset]; exact openGraph_le ω dt.adj)
  rw [if_pos dt.adj] at hterm
  have hbu : Section3.extend C u dt.snd = Section3.extend C u z := by linarith
  have hbx : dt.snd = x₀ := by
    by_contra hbx
    exact hb ⟨hbC, (hnbr _ dt.adj).2, hbx, hbu⟩
  rw [← hbx, hbu]

/-- Maximum principle with a single exit: a harmonic function is constant on the finite set
`𝒞 \ T` whose open edges to `T` all pass through one site `x₀`. -/
theorem exists_const_of_single_exit {ω : Configuration d} (C : OpenComponent ω)
    {T : Set (Vertex d)} (hTne : T.Nonempty) (hT : T ⊆ C.supp) (hfin : (C.supp \ T).Finite)
    {x₀ : Vertex d} (hall : ∀ z w, z ∈ T → w ∉ T → (openGraph ω).Adj z w → w = x₀)
    {u : C → ℝ} (hu : ∀ x, componentLaplacian C u x = 0) :
    ∃ k : ℝ, ∀ x : C, x.1 ∉ T → u x = k := by
  obtain ⟨t, ht⟩ := hTne
  rcases (C.supp \ T).eq_empty_or_nonempty with hP | hP
  · refine ⟨0, fun x hx => ?_⟩
    have hx' : x.1 ∈ C.supp \ T := ⟨x.2, hx⟩
    rw [hP] at hx'
    exact absurd hx' (Set.notMem_empty _)
  obtain ⟨zM, ⟨hzMC, hzMT⟩, hM⟩ := Set.exists_max_image _ (Section3.extend C u) hfin hP
  obtain ⟨zm, ⟨hzmC, hzmT⟩, hm⟩ := Set.exists_min_image _ (Section3.extend C u) hfin hP
  have h1 := extend_eq_of_isMaxOn C ht hT hall hu hzMC hzMT fun y hy hyT => hM y ⟨hy, hyT⟩
  have hneg : ∀ y, Section3.extend C (fun x => -u x) y = -Section3.extend C u y := by
    intro y
    by_cases hy : y ∈ C.supp
    · rw [extend_of_mem hy, extend_of_mem hy]
    · rw [extend_of_not_mem hy, extend_of_not_mem hy, neg_zero]
  have h2 := extend_eq_of_isMaxOn C ht hT hall
    (fun x => by rw [componentLaplacian_neg', hu x, neg_zero]) hzmC hzmT
    (fun y hy hyT => by rw [hneg, hneg]; exact neg_le_neg (hm y ⟨hy, hyT⟩))
  rw [hneg, hneg, neg_inj] at h2
  refine ⟨Section3.extend C u x₀, fun x hx => ?_⟩
  have hx' : Section3.extend C u x.1 = u x := extend_of_mem x.2
  have hlo := hm x.1 ⟨x.2, hx⟩
  have hhi := hM x.1 ⟨x.2, hx⟩
  rw [← hx']
  linarith

/-- Liouville case: if `ℓ̃_q` takes the single value `c` at the boundary edges, then `ℓ_q` is
constant on `F = 𝒞_∞ \ 𝒞̃_∞`. The function `v` equal to `ℓ̃_q` on `𝒞̃_∞` and to `c` on `F` is
harmonic on `𝒞_∞`, and `ℓ_q - v` is harmonic and sublinear. -/
theorem exists_const_of_boundary_const {R : ℕ} {q : Fin d → ℝ} {ω : Configuration d}
    (C : OpenComponent ω) (C' : OpenComponent (closedNear R ω)) (hC' : C'.supp.Infinite)
    (hsub : C'.supp ⊆ C.supp) (hfin : (C.supp \ C'.supp).Finite)
    (hliou : ∀ v : C → ℝ, (∀ x, componentLaplacian C v x = 0) →
      componentSlopeAsymptotics C 0 v → ∃ c : ℝ, ∀ x, v x = c)
    {ℓ : C → ℝ} (hℓ : IsCorrectedPlane C q ℓ) {ℓ' : C' → ℝ} (hℓ' : IsCorrectedPlane C' q ℓ')
    (c : ℝ) (hc : ∀ z w (hz : z ∈ C'.supp), w ∉ C'.supp → (openGraph ω).Adj z w →
      ℓ' ⟨z, hz⟩ = c) :
    ∃ k : ℝ, ∀ x : C, x.1 ∉ C'.supp → ℓ x = k := by
  classical
  let g : Vertex d → ℝ := fun y => if y ∈ C'.supp then Section3.extend C' ℓ' y else c
  let v : C → ℝ := fun x => g x.1
  have hextv : ∀ y, y ∈ C.supp → Section3.extend C v y = g y := fun y hy => extend_of_mem hy
  have hℓ'h := ((mem_harmonicGrowthSpace_iff _ _ _).mp hℓ'.1).1
  have hℓh := ((mem_harmonicGrowthSpace_iff _ _ _).mp hℓ.1).1
  -- `v` is harmonic on `𝒞_∞`
  have hv : ∀ x, componentLaplacian C v x = 0 := by
    rintro ⟨x, hx⟩
    rw [componentLaplacian_eq_sum_lattice C v x hx, hextv x hx]
    by_cases hx' : x ∈ C'.supp
    · have hxR := not_mem_cube_of_mem_supp C' hC' hx'
      have h0 := hℓ'h ⟨x, hx'⟩
      rw [componentLaplacian_eq_sum_lattice C' ℓ' x hx'] at h0
      refine (Finset.sum_congr rfl fun y _ => ?_).trans h0
      by_cases h1 : (openGraph (closedNear R ω)).Adj x y
      · have hy' : y ∈ C'.supp := C'.mem_supp_of_adj_mem_supp hx' h1
        rw [if_pos (closedNear_adj_iff.mp h1).1, if_pos h1, hextv y (hsub hy')]
        simp only [g, if_pos hy', if_pos hx']
      · rw [if_neg h1]
        split_ifs with hω
        · have hyC : y ∈ C.supp := C.mem_supp_of_adj_mem_supp hx hω
          have hy' : y ∉ C'.supp := fun hy' =>
            h1 (closedNear_adj_iff.mpr ⟨hω, hxR, not_mem_cube_of_mem_supp C' hC' hy'⟩)
          rw [hextv y hyC]
          simp only [g, if_neg hy', if_pos hx', extend_of_mem hx', hc x y hx' hy' hω, sub_self]
        · rfl
    · refine Finset.sum_eq_zero fun y _ => ?_
      split_ifs with hω
      · have hyC : y ∈ C.supp := C.mem_supp_of_adj_mem_supp hx hω
        rw [hextv y hyC]
        by_cases hy' : y ∈ C'.supp
        · simp only [g, if_pos hy', if_neg hx', extend_of_mem hy', hc y x hy' hx' hω.symm,
            sub_self]
        · simp only [g, if_neg hy', if_neg hx', sub_self]
      · rfl
  -- `ℓ_q - v` is sublinear
  obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ x : C, x.1 ∉ C'.supp → |ℓ x - c| ≤ K := by
    refine ⟨∑ y ∈ hfin.toFinset, |Section3.extend C ℓ y - c|, fun x hx => ?_⟩
    have hmem : x.1 ∈ hfin.toFinset := (Set.Finite.mem_toFinset _).mpr ⟨x.2, hx⟩
    have := Finset.single_le_sum (f := fun y => |Section3.extend C ℓ y - c|) (fun _ _ => abs_nonneg _) hmem
    have hx1 : Section3.extend C ℓ x.1 = ℓ x := extend_of_mem x.2
    rw [hx1] at this
    exact this
  have hsl : componentSlopeAsymptotics C 0 (fun x => ℓ x - v x) := by
    intro ε hε
    obtain ⟨R₁, hR₁, h1⟩ := hℓ.2 (ε / 2) (by positivity)
    obtain ⟨R₂, hR₂, h2⟩ := hℓ'.2 (ε / 2) (by positivity)
    refine ⟨max (max R₁ R₂) (K / ε), lt_max_of_lt_left (lt_max_of_lt_left hR₁), ?_⟩
    intro r hr x hx
    simp only [max_le_iff] at hr
    obtain ⟨⟨hr1, hr2⟩, hr3⟩ := hr
    have hs0 : componentSlope C 0 x = 0 := by simp [componentSlope]
    beta_reduce
    rw [hs0, sub_zero]
    by_cases hx' : x.1 ∈ C'.supp
    · have hvx : v x = ℓ' ⟨x.1, hx'⟩ := by
        show (if x.1 ∈ C'.supp then Section3.extend C' ℓ' x.1 else c) = _
        rw [if_pos hx', extend_of_mem hx']
      have hb' : (⟨x.1, hx'⟩ : C') ∈ componentEuclideanBall C' 0 r := by
        rw [mem_componentEuclideanBall] at hx ⊢
        exact hx
      have e1 := h1 r hr1 x hx
      have e2 := h2 r hr2 _ hb'
      have hsl : componentSlope C' q ⟨x.1, hx'⟩ = componentSlope C q x := rfl
      rw [hsl] at e2
      rw [hvx]
      calc |ℓ x - ℓ' ⟨x.1, hx'⟩|
          = |(ℓ x - componentSlope C q x) - (ℓ' ⟨x.1, hx'⟩ - componentSlope C q x)| := by ring_nf
        _ ≤ |ℓ x - componentSlope C q x| + |ℓ' ⟨x.1, hx'⟩ - componentSlope C q x| :=
          abs_sub _ _
        _ ≤ ε / 2 * r + ε / 2 * r := add_le_add e1 e2
        _ = ε * r := by ring
    · have hvx : v x = c := by
        show (if x.1 ∈ C'.supp then Section3.extend C' ℓ' x.1 else c) = _
        rw [if_neg hx']
      rw [hvx]
      calc |ℓ x - c| ≤ K := hK x hx'
        _ ≤ ε * r := by
          have := (div_le_iff₀ hε).mp hr3
          linarith
  obtain ⟨k, hk⟩ := hliou _ (fun x => by rw [Rigidity.Steps.S3.componentLaplacian_sub, hℓh x, hv x, sub_zero]) hsl
  refine ⟨k + c, fun x hx => ?_⟩
  have := hk x
  have hvx : v x = c := by
    show (if x.1 ∈ C'.supp then Section3.extend C' ℓ' x.1 else c) = _
    rw [if_neg hx]
  simp only [hvx] at this
  linarith

/-- **Closed-boundary argument** (deterministic part of `step:4.8-closed-boundary`). Let `𝒞̃_∞` be
the unique infinite cluster of `ω̃`, inside the cluster `𝒞_∞` of `ω` on which the Liouville theorem
at order zero holds, and let `ℓ_q`, `ℓ̃_q` be corrected planes of slope `q` of `𝒞_∞`, `𝒞̃_∞`, with
`ℓ_q` not constant on `Q_R ∩ 𝒞_∞`. Then two boundary placements `(x, x̃)`, `(y, ỹ)` with `x ≠ y`
have `x̃, ỹ ∈ 𝒞̃_∞` and `ℓ̃_q(x̃) ≠ ℓ̃_q(ỹ)`. -/
theorem exists_closedBoundary_pairs {R : ℕ} {q : Fin d → ℝ} {ω : Configuration d}
    (C : OpenComponent ω) (C' : OpenComponent (closedNear R ω)) (hC' : C'.supp.Infinite)
    (huniq : ∀ D : OpenComponent (closedNear R ω), D.supp.Infinite → D = C')
    (hsub : C'.supp ⊆ C.supp)
    (hliou : ∀ v : C → ℝ, (∀ x, componentLaplacian C v x = 0) →
      componentSlopeAsymptotics C 0 v → ∃ c : ℝ, ∀ x, v x = c)
    {ℓ : C → ℝ} (hℓ : IsCorrectedPlane C q ℓ)
    (hℓQ : ∃ x y : C, x.1 ∈ cube d R ∧ y.1 ∈ cube d R ∧ ℓ x ≠ ℓ y)
    {ℓ' : C' → ℝ} (hℓ' : IsCorrectedPlane C' q ℓ') :
    ∃ x x' y y' : Vertex d, (x, x') ∈ boundaryPairs d R ∧ (y, y') ∈ boundaryPairs d R ∧
      x ≠ y ∧ ∃ (hx' : x' ∈ C'.supp) (hy' : y' ∈ C'.supp), ℓ' ⟨x', hx'⟩ ≠ ℓ' ⟨y', hy'⟩ := by
  by_contra hneg
  suffices hconst : ∃ k : ℝ, ∀ x : C, x.1 ∉ C'.supp → ℓ x = k by
    obtain ⟨k, hk⟩ := hconst
    obtain ⟨x, y, hx, hy, hxy⟩ := hℓQ
    exact hxy ((hk x fun h => not_mem_cube_of_mem_supp C' hC' h hx).trans
      (hk y fun h => not_mem_cube_of_mem_supp C' hC' h hy).symm)
  have hfin := finite_supp_diff C C' hC' huniq hsub
  have hno : ∀ z₁ w₁ z₂ w₂ (hz₁ : z₁ ∈ C'.supp) (hz₂ : z₂ ∈ C'.supp), w₁ ∉ C'.supp →
      w₂ ∉ C'.supp → (openGraph ω).Adj z₁ w₁ → (openGraph ω).Adj z₂ w₂ →
      ℓ' ⟨z₁, hz₁⟩ ≠ ℓ' ⟨z₂, hz₂⟩ → w₁ = w₂ := by
    intro z₁ w₁ z₂ w₂ hz₁ hz₂ hw₁ hw₂ h₁ h₂ hne
    by_contra hw
    exact hneg ⟨w₁, z₁, w₂, z₂, mem_boundaryPairs_of_adj C' hC' hz₁ hw₁ h₁,
      mem_boundaryPairs_of_adj C' hC' hz₂ hw₂ h₂, hw, hz₁, hz₂, hne⟩
  by_cases hb : ∃ z₁ w₁ z₂ w₂, ∃ (hz₁ : z₁ ∈ C'.supp) (hz₂ : z₂ ∈ C'.supp), w₁ ∉ C'.supp ∧
      w₂ ∉ C'.supp ∧ (openGraph ω).Adj z₁ w₁ ∧ (openGraph ω).Adj z₂ w₂ ∧
      ℓ' ⟨z₁, hz₁⟩ ≠ ℓ' ⟨z₂, hz₂⟩
  · -- all boundary edges pass through one site: maximum principle
    obtain ⟨z₁, w₁, z₂, w₂, hz₁, hz₂, hw₁, hw₂, h₁, h₂, hne⟩ := hb
    have h12 := hno _ _ _ _ hz₁ hz₂ hw₁ hw₂ h₁ h₂ hne
    have hall : ∀ z w, z ∈ C'.supp → w ∉ C'.supp → (openGraph ω).Adj z w → w = w₁ := by
      intro z w hz hw hzw
      by_cases hval : ℓ' ⟨z, hz⟩ = ℓ' ⟨z₁, hz₁⟩
      · exact (hno _ _ _ _ hz hz₂ hw hw₂ hzw h₂ (hval ▸ hne)).trans h12.symm
      · exact hno _ _ _ _ hz hz₁ hw hw₁ hzw h₁ hval
    exact exists_const_of_single_exit C hC'.nonempty hsub hfin hall
      ((mem_harmonicGrowthSpace_iff _ _ _).mp hℓ.1).1
  · -- `ℓ̃_q` is constant at the boundary edges: Liouville
    obtain ⟨c, hc⟩ : ∃ c : ℝ, ∀ z w (hz : z ∈ C'.supp), w ∉ C'.supp →
        (openGraph ω).Adj z w → ℓ' ⟨z, hz⟩ = c := by
      by_cases hex : ∃ z w, ∃ hz : z ∈ C'.supp, w ∉ C'.supp ∧ (openGraph ω).Adj z w
      · obtain ⟨z₀, w₀, hz₀, hw₀, h₀⟩ := hex
        refine ⟨ℓ' ⟨z₀, hz₀⟩, fun z w hz hw hzw => ?_⟩
        by_contra hval
        exact hb ⟨z, w, z₀, w₀, hz, hz₀, hw, hw₀, hzw, h₀, hval⟩
      · exact ⟨0, fun z w hz hw hzw => absurd ⟨z, w, hz, hw, hzw⟩ hex⟩
    exact exists_const_of_boundary_const C C' hC' hsub hfin hliou hℓ hℓ' c hc

/-- **Step `step:4.8-closed-boundary`** (`ClosedBoundaryStep`, paper L1406-1411), for a slope
`q ≠ 0`: almost surely on `E_R`, after closing every bond meeting `Q_R`, two boundary placements
`(x, x̃)`, `(y, ỹ)` with `x ≠ y` have `x̃, ỹ ∈ 𝒞̃_∞` separated by a corrected plane `ℓ̃_q`. -/
theorem closedBoundaryStep [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) {q : Fin d → ℝ} (hq : q ≠ 0)
    (hAD : LatticeProb.External.ArmstrongDarioOrderZero)
    (hcorr : LatticeProb.External.SupercriticalBondCorrectorInput) :
    ClosedBoundaryStep d p q := by
  intro R
  have hU : ∀ᵐ ω ∂latticeBondLaw d p, HasUniqueInfiniteOpenComponent ω := by
    obtain ⟨_, _, _, _, _, _, X, _, _, _, _, hae⟩ := hAD d hd p hpc hp1
    filter_upwards [hae] with ω hω
    obtain ⟨hh, -⟩ := hω
    exact hh
  filter_upwards [ae_forall_closeBonds p hp1 hU, flipCorrectorStep hd p hpc hp1 hcorr,
    hcorr d hd p hpc hp1, sublinearLiouvilleStep hd p hpc hp1 hAD] with ω hUc hflip hcω hliou
  rintro ⟨-, h, hA1⟩
  set B := (finite_bondsNear d R).toFinset
  have hcl : closedNear R ω = Section3.closeBonds B ω := by
    funext e
    simp only [closedNear, Section3.closeBonds, B, Set.Finite.mem_toFinset]
  have h' : HasUniqueInfiniteOpenComponent (closedNear R ω) := hcl ▸ hUc B
  have hflip' : ∀ (h' : HasUniqueInfiniteOpenComponent (closedNear R ω))
      (o : uniqueInfiniteComponent h'),
      ∃! u, IsCorrectedPlane (uniqueInfiniteComponent h') q u ∧ u o = 0 := by
    rw [hcl]
    exact fun h' o => hflip B h' q o
  set C := uniqueInfiniteComponent h
  set C' := uniqueInfiniteComponent h'
  have hC' : C'.supp.Infinite := uniqueInfiniteComponent_infinite h'
  have huniq : ∀ D : OpenComponent (closedNear R ω), D.supp.Infinite → D = C' :=
    fun D hD => (eq_uniqueInfiniteComponent_iff h' D).mpr hD
  have hsub : C'.supp ⊆ C.supp := by
    obtain ⟨v, hv⟩ := hC'.nonempty
    have hsub := supp_subset_of_closedNear C' hv
    have hinf : ((openGraph ω).connectedComponentMk v).supp.Infinite := Set.Infinite.mono hsub hC'
    rwa [(eq_uniqueInfiniteComponent_iff h _).mpr hinf] at hsub
  -- the corrected planes `ℓ̃_q` of `𝒞̃_∞` and `ℓ_q` of `𝒞_∞`
  obtain ⟨o', ho'⟩ := hC'.nonempty
  obtain ⟨ℓ', ⟨hℓ', -⟩, -⟩ := hflip' h' ⟨o', ho'⟩
  obtain ⟨o, ho⟩ := (uniqueInfiniteComponent_infinite h).nonempty
  obtain ⟨hplanes, hslope⟩ := hcω h
  obtain ⟨ℓ, ⟨hℓ, -⟩, -⟩ := hplanes q ⟨o, ho⟩
  -- `ℓ_q` is not constant: its slope `q ≠ 0` is unique
  have hnc : ∃ x y : C, ℓ x ≠ ℓ y := by
    by_contra hcon
    push Not at hcon
    have hconst : ℓ = fun _ => ℓ ⟨o, ho⟩ := funext fun x => hcon x _
    obtain ⟨q₀, -, hq₀⟩ := hslope ℓ hℓ.1
    have e2 : IsCorrectedPlane C 0 ℓ := by
      rw [hconst]
      exact isCorrectedPlane_const C _
    exact hq ((hq₀ q hℓ).trans (hq₀ 0 e2).symm)
  obtain ⟨x, y, hx, hy, hxy⟩ := hA1 ℓ hℓ.1 hnc
  obtain ⟨a, a', b, b', ha, hb, hab, ha', hb', hne⟩ :=
    exists_closedBoundary_pairs C C' hC' huniq hsub (hliou h) hℓ ⟨x, y, hx, hy, hxy⟩ hℓ'
  exact ⟨a, a', b, b', ha, hb, hab, h', ha', hb', ℓ', hℓ', hne⟩

end Rigidity.Proofs.S4
