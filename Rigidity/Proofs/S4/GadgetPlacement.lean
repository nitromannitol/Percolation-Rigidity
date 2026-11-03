import Rigidity.Steps.S4.NonConstantOnGadget
import LatticeProb.Prob.Percolation.LatticeBondTranslation

/-!
# Lemma 4.8: the placement of the gadget (Figure `attach-gadget`)

The construction of `H` and `τ` in the proof of Lemma 4.8 (paper L1411-1413 of the corrected
draft, Figure `attach-gadget`), and the proofs of the two deterministic steps
`Rigidity.Steps.S4.AttachGeometryStep` and `Rigidity.Steps.S4.PlacementCountStep`.

Write `m = ⌊R/2⌋`. The gadget `T_R` (`OpenLadder.Embedding.ambientSites hd R`) is translated by
`τ_R = (-3, -m-2, 0, …)`: its bottom row `s, a, b, t` is `(-2, -m-1), …, (1, -m-1)`, just outside
`Q_m` (the adjacent sites `a, b` of the outer boundary of `Q_{R/2}`), and its rungs lie in `Q_m`.
So the gadget is a subgraph of `Q_{R/2} ∪ {s, a, b, t}`, as in the paper.

The paths `P₁, P₂` from the boundary sites `x ≠ y` to the terminals `s, t` are polygonal lattice
paths (`chainBonds`): staircases between consecutive waypoints (`attachWaypoints`). Pick a
coordinate `k` with `x_k ≠ y_k` and call `lo` (resp. `hi`) the site with the smaller (larger)
`k`-th coordinate. With `h = -m-2` and `c = m+2`:
* `P₁`: from `lo` move the `k`-th coordinate to `-R`, then cross the face `{z_k = -R}` of `Q_R` to
  `(-c, h, 0, …)` with `k`-th coordinate `-R`, then move the `k`-th coordinate to that of
  `(-c, h, 0, …)`, then go to `(-2, h, 0, …)` and up to `s`;
* `P₂`: the mirror image, from `hi` through the face `{z_k = R}` to `(c, h, 0, …)`, `(1, h, 0, …)`
  and `t`.
`P₁` and `P₂` avoid `Q_{R/2}`: their sites on `∂Q_R` satisfy `z_k ≤ lo_k`, resp. `z_k ≥ hi_k`,
and their other sites satisfy `z_0 ≤ -2`, resp. `z_0 ≥ 1`, so they are disjoint
(`attachPaths_spec`); they meet the gadget only at `s`, resp. `t`, and each contains a lattice
path from its boundary site to its terminal (`lowPath_walk`, `highPath_walk`). The paper's paths
end at the adjacent sites `a, b`; here they end at the leaves `s, t` of the gadget, whose only
gadget neighbours are `a, b`. Which of `x, y` is joined to `s` is fixed by the separating
coordinate; the Liouville argument of `AttachStep` is symmetric in `s, t`.

`H R x y` is the union of the bonds of the translated gadget and of `P₁, P₂`.
`AttachGeometryStep` asks that `H R x y` be a bond set of `Q_R` containing the translated
gadget as an induced subgraph, and that the gadget be isolated in it (inside `Q_{R-1}`, and the
paths attached at the terminals only, `attachBondSet_isolated`); `PlacementCountStep` counts the
boundary placements `(x, x̃)` by the coordinate and direction of `x̃ - x` and the other
coordinates of `x`.
-/

namespace Rigidity.Proofs.S4

open LatticeProb LatticeProb.Percolation LatticeProb.Network
  LatticeProb.Network.OpenLadder.Embedding Rigidity.Section4 Rigidity.Steps.S4

variable {d : ℕ}

/-! ### Polygonal lattice paths -/

/-- The corner of the staircase from `a` to `b` before its leg in direction `j`: the coordinates
below `j` are those of `b`, the others those of `a`. -/
def stairCorner (a b : Vertex d) (j : Fin d) : Vertex d := fun i => if i < j then b i else a i

/-- The bonds `{update z j v, update z j (v + 1)}` of the lattice segment through `z` in the
direction `j`, the `j`-th coordinate ranging between `u` and `w`. -/
def segmentBonds (z : Vertex d) (j : Fin d) (u w : ℤ) : Set (Bond d) :=
  {e | ∃ v : ℤ, min u w ≤ v ∧ v < max u w ∧
    (e : Sym2 (Vertex d)) = s(Function.update z j v, Function.update z j (v + 1))}

/-- The bonds of the staircase from `a` to `b`, which moves the coordinates one at a time, in
increasing order. -/
def stairBonds (a b : Vertex d) : Set (Bond d) :=
  ⋃ j : Fin d, segmentBonds (stairCorner a b j) j (a j) (b j)

/-- The bonds of the polygonal lattice path through a list of waypoints: the staircases between
consecutive waypoints. -/
def chainBonds : List (Vertex d) → Set (Bond d)
  | a :: b :: l => stairBonds a b ∪ chainBonds (b :: l)
  | _ => ∅

/-- The sites of a staircase lie in the box spanned by its ends. -/
theorem stairBonds_box {a b : Vertex d} {e : Bond d} (he : e ∈ stairBonds a b)
    {z : Vertex d} (hz : z ∈ (e : Sym2 (Vertex d))) (i : Fin d) :
    min (a i) (b i) ≤ z i ∧ z i ≤ max (a i) (b i) := by
  simp only [stairBonds, segmentBonds, Set.mem_iUnion, Set.mem_setOf_eq] at he
  obtain ⟨j, v, hv₁, hv₂, he⟩ := he
  rw [he, Sym2.mem_iff] at hz
  have hcorner : min (a i) (b i) ≤ stairCorner a b j i ∧ stairCorner a b j i ≤ max (a i) (b i) := by
    unfold stairCorner
    split_ifs
    · exact ⟨min_le_right _ _, le_max_right _ _⟩
    · exact ⟨min_le_left _ _, le_max_left _ _⟩
  rcases hz with rfl | rfl <;> rcases eq_or_ne i j with rfl | hij
  · rw [Function.update_self]
    exact ⟨hv₁, hv₂.le⟩
  · rwa [Function.update_of_ne hij]
  · rw [Function.update_self]
    exact ⟨by omega, by omega⟩
  · rwa [Function.update_of_ne hij]

/-- A staircase between two sites of `Q_R` stays in `Q_R`. -/
theorem stairBonds_cube {R : ℕ} {a b : Vertex d} (ha : a ∈ cube d R) (hb : b ∈ cube d R)
    {e : Bond d} (he : e ∈ stairBonds a b) {z : Vertex d} (hz : z ∈ (e : Sym2 (Vertex d))) :
    z ∈ cube d R := by
  intro i
  have h := stairBonds_box he hz i
  have ha' := abs_le.mp (ha i)
  have hb' := abs_le.mp (hb i)
  exact abs_le.mpr ⟨(le_min ha'.1 hb'.1).trans h.1, h.2.trans (max_le ha'.2 hb'.2)⟩

/-- A polygonal lattice path through sites of `Q_R` stays in `Q_R`. -/
theorem chainBonds_cube {R : ℕ} : ∀ {l : List (Vertex d)}, (∀ a ∈ l, a ∈ cube d R) →
    ∀ e ∈ chainBonds l, ∀ z ∈ (e : Sym2 (Vertex d)), z ∈ cube d R
  | a :: b :: l, hl, e, he, z, hz => by
    simp only [chainBonds, Set.mem_union] at he
    rcases he with he | he
    · exact stairBonds_cube (hl a (by simp)) (hl b (by simp)) he hz
    · exact chainBonds_cube (fun c hc => hl c (List.mem_cons_of_mem a hc)) e he z hz
  | [], _, e, he, _, _ => by simp [chainBonds] at he
  | [_], _, e, he, _, _ => by simp [chainBonds] at he

/-! ### The construction of Figure `attach-gadget` -/

/-- The half side `m = ⌊R/2⌋` of the cube `Q_{R/2}` of the paper. -/
def halfSide (R : ℕ) : ℤ := ((R / 2 : ℕ) : ℤ)

/-- The translation `τ_R = (-3, -m-2, 0, …)` of the gadget of height `R`: the terminals are
`s = (-2, -m-1)` and `t = (1, -m-1)`. -/
def gadgetShift (d R : ℕ) : Vertex d := zeroPad d (-3, -halfSide R - 2)

/-- The bonds of the gadget of height `R` translated by `τ_R`: the lattice bonds between two of its
sites (the gadget is an induced subgraph of `ℤ^d`, `OpenLadder.Embedding.ambientGraph`). -/
def gadgetBonds (hd : 2 ≤ d) (R : ℕ) : Set (Bond d) :=
  {e | ∀ z ∈ (e : Sym2 (Vertex d)), z - gadgetShift d R ∈ ambientSites hd (R : ℤ)}

open scoped Classical in
/-- A coordinate `k` with `x_k ≠ y_k` (the coordinate `0` if `x = y`). -/
noncomputable def sepCoord (hd : 2 ≤ d) (x y : Vertex d) : Fin d :=
  if h : ∃ i, x i ≠ y i then h.choose else ⟨0, by omega⟩

open scoped Classical in
/-- The site of `{x, y}` with the smaller `k`-th coordinate, `k = sepCoord hd x y`. -/
noncomputable def lowSite (hd : 2 ≤ d) (x y : Vertex d) : Vertex d :=
  if x (sepCoord hd x y) < y (sepCoord hd x y) then x else y

open scoped Classical in
/-- The site of `{x, y}` with the larger `k`-th coordinate, `k = sepCoord hd x y`. -/
noncomputable def highSite (hd : 2 ≤ d) (x y : Vertex d) : Vertex d :=
  if x (sepCoord hd x y) < y (sepCoord hd x y) then y else x

/-- The waypoints of the path `P₁` (`σ = -1`, `col = -2`, ending at `s`) or `P₂` (`σ = 1`,
`col = 1`, ending at `t`) from the boundary site `z`: move the `k`-th coordinate to `σ R`, cross
the face `{z_k = σ R}` of `Q_R`, leave it along the `k`-th coordinate at `(σ c, h, 0, …)`, then go
along the row `h = -m-2` to the column `col` and up to the terminal `(col, -m-1)`. -/
def attachWaypoints (R : ℕ) (k : Fin d) (σ col : ℤ) (z : Vertex d) : List (Vertex d) :=
  [z, Function.update z k (σ * R),
    Function.update (zeroPad d (σ * (halfSide R + 2), -halfSide R - 2)) k (σ * R),
    zeroPad d (σ * (halfSide R + 2), -halfSide R - 2), zeroPad d (col, -halfSide R - 2),
    zeroPad d (col, -halfSide R - 1)]

/-- The bonds of the path `P₁` of Figure `attach-gadget`, from the low site to `s`. -/
noncomputable def lowPathBonds (hd : 2 ≤ d) (R : ℕ) (x y : Vertex d) : Set (Bond d) :=
  chainBonds (attachWaypoints R (sepCoord hd x y) (-1) (-2) (lowSite hd x y))

/-- The bonds of the path `P₂` of Figure `attach-gadget`, from the high site to `t`. -/
noncomputable def highPathBonds (hd : 2 ≤ d) (R : ℕ) (x y : Vertex d) : Set (Bond d) :=
  chainBonds (attachWaypoints R (sepCoord hd x y) 1 1 (highSite hd x y))

/-- The bond set `H` of Figure `attach-gadget`: the gadget of height `R` translated by `τ_R`, and
the paths `P₁` from the low site to `s` and `P₂` from the high site to `t`. -/
noncomputable def attachBondSet (hd : 2 ≤ d) (R : ℕ) (x y : Vertex d) : Set (Bond d) :=
  gadgetBonds hd R ∪ lowPathBonds hd R x y ∪ highPathBonds hd R x y

/-- The sites of the bonds of `B`. -/
def bondSites (B : Set (Bond d)) : Set (Vertex d) := {z | ∃ e ∈ B, z ∈ (e : Sym2 (Vertex d))}

/-! ### `step:4.8-attach`, geometry -/

theorem zeroPad_mem_cube {R : ℕ} {a b : ℤ} (ha : |a| ≤ R) (hb : |b| ≤ R) :
    zeroPad d (a, b) ∈ cube d R := by
  intro i
  simp only [zeroPad]
  split_ifs
  · exact ha
  · exact hb
  · simp

theorem update_mem_cube {R : ℕ} {z : Vertex d} (hz : z ∈ cube d R) (k : Fin d) {v : ℤ}
    (hv : |v| ≤ R) : Function.update z k v ∈ cube d R := by
  intro i
  rw [Function.update_apply]
  split_ifs
  · exact hv
  · exact hz i

theorem attachWaypoints_cube {R : ℕ} (hR : 4 ≤ R) (k : Fin d) {σ col : ℤ}
    (hσ : σ = 1 ∨ σ = -1) (hcol : |col| ≤ 2) {z : Vertex d} (hz : z ∈ cube d R) :
    ∀ a ∈ attachWaypoints R k σ col z, a ∈ cube d R := by
  have hm : 2 * halfSide R ≤ R ∧ 0 ≤ halfSide R := by unfold halfSide; omega
  have hσR : |σ * R| ≤ R := by rcases hσ with rfl | rfl <;> simp
  have hc : |σ * (halfSide R + 2)| ≤ R := by
    rcases hσ with rfl | rfl <;> simp only [one_mul, neg_one_mul, abs_neg] <;>
      rw [abs_le] <;> constructor <;> omega
  have hh : |-halfSide R - 2| ≤ R := by rw [abs_le]; constructor <;> omega
  have hh' : |-halfSide R - 1| ≤ R := by rw [abs_le]; constructor <;> omega
  have hcol' : |col| ≤ R := by omega
  simp only [attachWaypoints, List.mem_cons, List.not_mem_nil, or_false]
  rintro a (rfl | rfl | rfl | rfl | rfl | rfl)
  · exact hz
  · exact update_mem_cube hz k hσR
  · exact update_mem_cube (zeroPad_mem_cube hc hh) k hσR
  · exact zeroPad_mem_cube hc hh
  · exact zeroPad_mem_cube hcol' hh
  · exact zeroPad_mem_cube hcol' hh'

/-- The translated gadget lies in `Q_R`. -/
theorem gadget_mem_cube (hd : 2 ≤ d) {R : ℕ} (hR : 4 ≤ R) {g : Vertex d}
    (hg : g ∈ ambientSites hd (R : ℤ)) : gadgetShift d R + g ∈ cube d R := by
  obtain ⟨hg01, hg2⟩ := hg
  have hm : 2 * halfSide R ≤ R ∧ (R : ℤ) ≤ 2 * halfSide R + 1 := by unfold halfSide; omega
  have hd0 : 0 < d := by omega
  have hd1 : 1 < d := by omega
  intro i
  simp only [Pi.add_apply, gadgetShift, zeroPad]
  rw [abs_le]
  by_cases h0 : i.val = 0
  · obtain rfl : i = ⟨0, hd0⟩ := Fin.ext h0
    simp only [if_true]
    constructor <;> omega
  · by_cases h1 : i.val = 1
    · obtain rfl : i = ⟨1, hd1⟩ := Fin.ext h1
      simp only [if_true, one_ne_zero, if_false]
      constructor <;> omega
    · rw [if_neg h0, if_neg h1, hg2 i (by omega)]
      constructor <;> omega

theorem lowSite_mem {hd : 2 ≤ d} {x y : Vertex d} {S : Set (Vertex d)} (hx : x ∈ S)
    (hy : y ∈ S) : lowSite hd x y ∈ S := by
  unfold lowSite; split_ifs <;> assumption

theorem highSite_mem {hd : 2 ≤ d} {x y : Vertex d} {S : Set (Vertex d)} (hx : x ∈ S)
    (hy : y ∈ S) : highSite hd x y ∈ S := by
  unfold highSite; split_ifs <;> assumption

/-- The translated gadget lies in `Q_{R-1}`. -/
theorem gadget_mem_cube_pred (hd : 2 ≤ d) {R : ℕ} (hR : 4 ≤ R) {g : Vertex d}
    (hg : g ∈ ambientSites hd (R : ℤ)) : gadgetShift d R + g ∈ cube d (R - 1) := by
  obtain ⟨hg01, hg2⟩ := hg
  have hm : 2 * halfSide R ≤ R ∧ (R : ℤ) ≤ 2 * halfSide R + 1 := by unfold halfSide; omega
  have hR1 : ((R - 1 : ℕ) : ℤ) = R - 1 := by omega
  have hd0 : 0 < d := by omega
  have hd1 : 1 < d := by omega
  intro i
  simp only [Pi.add_apply, gadgetShift, zeroPad, hR1]
  rw [abs_le]
  by_cases h0 : i.val = 0
  · obtain rfl : i = ⟨0, hd0⟩ := Fin.ext h0
    simp only [if_true]
    constructor <;> omega
  · by_cases h1 : i.val = 1
    · obtain rfl : i = ⟨1, hd1⟩ := Fin.ext h1
      simp only [if_true, one_ne_zero, if_false]
      constructor <;> omega
    · rw [if_neg h0, if_neg h1, hg2 i (by omega)]
      constructor <;> omega

/-- For `R ≥ 4` the bond set `H R x y` of Figure `attach-gadget` lies in `Q_R` and contains the
gadget of height `R`, translated by `τ_R` inside `Q_R`, as an induced subgraph. -/
theorem attachBondSet_isGadgetPlacement (hd : 2 ≤ d) {R : ℕ} (hR : 4 ≤ R) {x x' y y' : Vertex d}
    (hx : (x, x') ∈ boundaryPairs d R) (hy : (y, y') ∈ boundaryPairs d R) :
    IsGadgetPlacement hd R (attachBondSet hd R x y) (gadgetShift d R) := by
  refine ⟨?_, fun g hg => gadget_mem_cube hd hR hg, ?_⟩
  · intro e he z hz
    rcases he with (he | he) | he
    · have := gadget_mem_cube hd hR (he z hz)
      rwa [add_sub_cancel] at this
    · exact chainBonds_cube (attachWaypoints_cube hR _ (Or.inr rfl) (by norm_num)
        (lowSite_mem hx.1 hy.1)) e he z hz
    · exact chainBonds_cube (attachWaypoints_cube hR _ (Or.inl rfl) (by norm_num)
        (highSite_mem hx.1 hy.1)) e he z hz
  · intro g hg g' hg' hadj
    constructor
    · intro _
      rw [ambientGraph, SimpleGraph.induce_adj]
      rw [add_comm (gadgetShift d R) g, add_comm (gadgetShift d R) g'] at hadj
      exact (nearestNeighborGraph_adj_add_iff g g' _).mp hadj
    · intro _
      left; left
      intro z hz
      simp only [bondOfAdjacent, Sym2.mem_iff] at hz
      rcases hz with rfl | rfl
      · simpa using hg
      · simpa using hg'

/-! ### The paths `P₁`, `P₂` of Figure `attach-gadget` -/

/-- Where the sites of the path from `z₀` with orientation `σ` lie: on `∂Q_R`, on the side
`σ z_k ≥ σ z₀_k` of `z₀`, or strictly inside `Q_R`, on the side `σ z_0 ≥ 1`, and either outside
`Q_{m+1}` or on the row `z_1 ≤ -m-2`, or at the terminal `(col, -m-1)`. -/
def PathSiteSpec (hd : 2 ≤ d) (R : ℕ) (k : Fin d) (σ col : ℤ) (z₀ z : Vertex d) : Prop :=
  ((∃ i, z i = R ∨ z i = -R) ∧ σ * z₀ k ≤ σ * z k) ∨
    ((∀ i, -(R : ℤ) < z i ∧ z i < R) ∧ 1 ≤ σ * z ⟨0, by omega⟩ ∧
      (halfSide R + 2 ≤ z ⟨0, by omega⟩ ∨ z ⟨0, by omega⟩ ≤ -halfSide R - 2 ∨
        z ⟨1, by omega⟩ ≤ -halfSide R - 2 ∨ z = zeroPad d (col, -halfSide R - 1)))

theorem zeroPad_apply (p : ℤ × ℤ) (i : Fin d) :
    zeroPad d p i = if i.val = 0 then p.1 else if i.val = 1 then p.2 else 0 := rfl

/-- The sites of the path from a boundary site `z₀` with orientation `σ = ± 1` satisfy
`PathSiteSpec`, provided `z₀` stays on `∂Q_R` when its `k`-th coordinate moves to `σ R`. -/
theorem attachWaypoints_sites (hd : 2 ≤ d) {R : ℕ} (hR : 5 ≤ R) (k : Fin d) {σ col : ℤ}
    (hσ : (σ = -1 ∧ col = -2) ∨ (σ = 1 ∧ col = 1)) {z₀ : Vertex d} (hz₀ : z₀ ∈ cube d R)
    (hbd : (∃ i, i ≠ k ∧ (z₀ i = R ∨ z₀ i = -R)) ∨ z₀ k = σ * R) :
    ∀ e ∈ chainBonds (attachWaypoints R k σ col z₀), ∀ z ∈ (e : Sym2 (Vertex d)),
      PathSiteSpec hd R k σ col z₀ z := by
  have hm : 2 * halfSide R ≤ R ∧ (R : ℤ) ≤ 2 * halfSide R + 1 := by unfold halfSide; omega
  have hd0 : 0 < d := by omega
  have hd1 : 1 < d := by omega
  have hz₀k := abs_le.mp (hz₀ k)
  intro e he z hz
  simp only [attachWaypoints, chainBonds, Set.mem_union, Set.mem_empty_iff_false,
    or_false] at he
  rcases he with he | he | he | he | he <;> have hbox := stairBonds_box he hz <;> clear he hz
  · -- leave `z₀` along the `k`-th coordinate
    left
    have hk := hbox k
    simp only [Function.update_self] at hk
    rcases hbd with ⟨i, hik, hi⟩ | hk'
    · refine ⟨⟨i, ?_⟩, by rcases hσ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega⟩
      have := hbox i
      simp only [Function.update_of_ne hik] at this
      omega
    · refine ⟨⟨k, ?_⟩, ?_⟩ <;> rcases hσ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
  · -- cross the face `{z_k = σ R}`
    clear hbd
    left
    have hk := hbox k
    simp only [Function.update_self] at hk
    refine ⟨⟨k, ?_⟩, ?_⟩ <;> rcases hσ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
  · -- leave the face along the `k`-th coordinate
    clear hbd
    by_cases hzk : z k = σ * R
    · left
      refine ⟨⟨k, ?_⟩, ?_⟩ <;> rcases hσ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
    right
    have hin : ∀ i, -(R : ℤ) < z i ∧ z i < R := by
      intro i
      have := hbox i
      rcases eq_or_ne i k with rfl | hik
      · simp only [Function.update_self, zeroPad_apply] at this
        split_ifs at this <;> rcases hσ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
      · simp only [Function.update_of_ne hik, zeroPad_apply] at this
        split_ifs at this <;> rcases hσ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
    refine ⟨hin, ?_⟩
    have h0 := hbox ⟨0, hd0⟩
    have h1 := hbox ⟨1, hd1⟩
    rcases eq_or_ne (⟨0, hd0⟩ : Fin d) k with h0k | h0k
    · subst h0k
      have h1k : (⟨1, hd1⟩ : Fin d) ≠ ⟨0, hd0⟩ := by simp [Fin.ext_iff]
      simp only [Function.update_self, Function.update_of_ne h1k, zeroPad_apply] at h0 h1
      simp only [if_true, one_ne_zero, if_false] at h0 h1
      have := hin ⟨0, hd0⟩
      rcases hσ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
    · simp only [Function.update_of_ne h0k, zeroPad_apply, if_true] at h0
      rcases eq_or_ne (⟨1, hd1⟩ : Fin d) k with h1k | h1k
      · rcases hσ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
      · simp only [Function.update_of_ne h1k, zeroPad_apply, one_ne_zero, if_true,
          if_false] at h1
        rcases hσ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
  · -- along the row `h = -m-2` to the column `col`
    clear hbd
    right
    have h0 := hbox ⟨0, hd0⟩
    have h1 := hbox ⟨1, hd1⟩
    simp only [zeroPad_apply, if_true, one_ne_zero, if_false] at h0 h1
    refine ⟨fun i => ?_, ?_⟩
    · have := hbox i
      simp only [zeroPad_apply] at this
      split_ifs at this <;> rcases hσ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
    · rcases hσ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
  · -- up the column `col` to the terminal
    clear hbd
    right
    have h0 := hbox ⟨0, hd0⟩
    have h1 := hbox ⟨1, hd1⟩
    simp only [zeroPad_apply, if_true, one_ne_zero, if_false] at h0 h1
    refine ⟨fun i => ?_, by rcases hσ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega, ?_⟩
    · have := hbox i
      simp only [zeroPad_apply] at this
      split_ifs at this <;> rcases hσ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
    · by_cases hz1 : z ⟨1, hd1⟩ = -halfSide R - 1
      · right; right; right
        funext i
        have := hbox i
        rw [zeroPad_apply]
        simp only [zeroPad_apply] at this
        by_cases hi0 : i.val = 0
        · obtain rfl : i = ⟨0, hd0⟩ := Fin.ext hi0
          simp only [if_true] at this ⊢
          omega
        · by_cases hi1 : i.val = 1
          · obtain rfl : i = ⟨1, hd1⟩ := Fin.ext hi1
            simp only [if_true, one_ne_zero, if_false] at this ⊢
            exact hz1
          · simp only [hi0, hi1, if_false] at this ⊢
            omega
      · right; right; left
        omega

/-- A boundary placement `(x, x̃)` has `x ∈ ∂Q_R`: some coordinate of `x` is `± R`. -/
theorem boundaryPairs_extreme {R : ℕ} {x x' : Vertex d} (hx : (x, x') ∈ boundaryPairs d R) :
    ∃ i, x i = R ∨ x i = -R := by
  obtain ⟨hxQ, hx'Q, i, hadj⟩ := hx
  dsimp only at hxQ hx'Q hadj
  refine ⟨i, ?_⟩
  have hout : ∀ j, j ≠ i → x' j = x j := by
    intro j hj
    rcases hadj with rfl | rfl <;> simp [unit, hj]
  have hxi : ¬ |x' i| ≤ R := by
    intro h
    apply hx'Q
    intro j
    by_cases hj : j = i
    · subst hj; exact h
    · rw [hout j hj]; exact hxQ j
  rw [abs_le] at hxi
  have hxi' := abs_le.mp (hxQ i)
  rcases hadj with h | h
  · have : x' i = x i + 1 := by rw [h]; simp [unit]
    omega
  · have : x i = x' i + 1 := by rw [h]; simp [unit]
    omega

theorem sepCoord_ne (hd : 2 ≤ d) {x y : Vertex d} (hxy : x ≠ y) :
    x (sepCoord hd x y) ≠ y (sepCoord hd x y) := by
  have h : ∃ i, x i ≠ y i := by
    by_contra! h
    exact hxy (funext h)
  unfold sepCoord
  rw [dif_pos h]
  exact h.choose_spec

theorem lowSite_lt_highSite (hd : 2 ≤ d) {x y : Vertex d} (hxy : x ≠ y) :
    lowSite hd x y (sepCoord hd x y) < highSite hd x y (sepCoord hd x y) := by
  have := sepCoord_ne hd hxy
  unfold lowSite highSite
  split_ifs with h
  · exact h
  · omega

/-- The sites of `P₁` satisfy `PathSiteSpec` with `σ = -1`, those of `P₂` with `σ = 1`. -/
theorem lowPath_sites (hd : 2 ≤ d) {R : ℕ} (hR : 5 ≤ R) {x x' y y' : Vertex d}
    (hx : (x, x') ∈ boundaryPairs d R) (hy : (y, y') ∈ boundaryPairs d R) (hxy : x ≠ y) :
    ∀ z ∈ bondSites (lowPathBonds hd R x y),
      PathSiteSpec hd R (sepCoord hd x y) (-1) (-2) (lowSite hd x y) z := by
  rintro z ⟨e, he, hz⟩
  have hlt := lowSite_lt_highSite hd hxy
  have hQ : highSite hd x y ∈ cube d R := highSite_mem hx.1 hy.1
  have hhi := abs_le.mp (hQ (sepCoord hd x y))
  refine attachWaypoints_sites hd hR _ (Or.inl ⟨rfl, rfl⟩)
    (lowSite_mem (x := x) (y := y) hx.1 hy.1) ?_ e he z hz
  obtain ⟨i, hi⟩ : ∃ i, lowSite hd x y i = R ∨ lowSite hd x y i = -R :=
    lowSite_mem (S := {z : Vertex d | ∃ i, z i = R ∨ z i = -R}) (boundaryPairs_extreme hx)
      (boundaryPairs_extreme hy)
  rcases eq_or_ne i (sepCoord hd x y) with rfl | hik
  · right; omega
  · exact Or.inl ⟨i, hik, hi⟩

theorem highPath_sites (hd : 2 ≤ d) {R : ℕ} (hR : 5 ≤ R) {x x' y y' : Vertex d}
    (hx : (x, x') ∈ boundaryPairs d R) (hy : (y, y') ∈ boundaryPairs d R) (hxy : x ≠ y) :
    ∀ z ∈ bondSites (highPathBonds hd R x y),
      PathSiteSpec hd R (sepCoord hd x y) 1 1 (highSite hd x y) z := by
  rintro z ⟨e, he, hz⟩
  have hlt := lowSite_lt_highSite hd hxy
  have hQ : lowSite hd x y ∈ cube d R := lowSite_mem hx.1 hy.1
  have hlo := abs_le.mp (hQ (sepCoord hd x y))
  refine attachWaypoints_sites hd hR _ (Or.inr ⟨rfl, rfl⟩)
    (highSite_mem (x := x) (y := y) hx.1 hy.1) ?_ e he z hz
  obtain ⟨i, hi⟩ : ∃ i, highSite hd x y i = R ∨ highSite hd x y i = -R :=
    highSite_mem (S := {z : Vertex d | ∃ i, z i = R ∨ z i = -R}) (boundaryPairs_extreme hx)
      (boundaryPairs_extreme hy)
  rcases eq_or_ne i (sepCoord hd x y) with rfl | hik
  · right; omega
  · exact Or.inl ⟨i, hik, hi⟩

/-- The paths `P₁` and `P₂` of Figure `attach-gadget` are vertex-disjoint. -/
theorem attachPaths_disjoint (hd : 2 ≤ d) {R : ℕ} (hR : 5 ≤ R) {x x' y y' : Vertex d}
    (hx : (x, x') ∈ boundaryPairs d R) (hy : (y, y') ∈ boundaryPairs d R) (hxy : x ≠ y) :
    Disjoint (bondSites (lowPathBonds hd R x y)) (bondSites (highPathBonds hd R x y)) := by
  rw [Set.disjoint_left]
  intro z h₁ h₂
  have hlt := lowSite_lt_highSite hd hxy
  rcases lowPath_sites hd hR hx hy hxy z h₁ with ⟨⟨i, hi⟩, h₁⟩ | ⟨hin₁, h₁, -⟩ <;>
    rcases highPath_sites hd hR hx hy hxy z h₂ with ⟨⟨j, hj⟩, h₂⟩ | ⟨hin₂, h₂, -⟩
  · omega
  · have := hin₂ i; omega
  · have := hin₁ j; omega
  · omega

/-- The sites of a path satisfying `PathSiteSpec` lie outside `Q_{R/2}`. -/
theorem PathSiteSpec.not_mem_cube {hd : 2 ≤ d} {R : ℕ} (hR : 5 ≤ R) {k : Fin d} {σ col : ℤ}
    {z₀ z : Vertex d} (h : PathSiteSpec hd R k σ col z₀ z) : z ∉ cube d (R / 2) := by
  have hm : 2 * halfSide R ≤ R ∧ (R : ℤ) ≤ 2 * halfSide R + 1 := by unfold halfSide; omega
  intro hz
  rcases h with ⟨⟨i, hi⟩, -⟩ | ⟨-, -, h | h | h | rfl⟩
  · have := abs_le.mp (hz i); unfold halfSide at hm; omega
  · have := abs_le.mp (hz ⟨0, by omega⟩); unfold halfSide at hm h; omega
  · have := abs_le.mp (hz ⟨0, by omega⟩); unfold halfSide at hm h; omega
  · have := abs_le.mp (hz ⟨1, by omega⟩); unfold halfSide at hm h; omega
  · have := abs_le.mp (hz ⟨1, by omega⟩)
    simp only [zeroPad_apply, one_ne_zero, if_true, if_false] at this
    unfold halfSide at hm this; omega

/-- A site of a path satisfying `PathSiteSpec` on the translated gadget is the terminal
`(col, -m-1)`. -/
theorem PathSiteSpec.eq_of_gadget {hd : 2 ≤ d} {R : ℕ} (hR : 5 ≤ R) {k : Fin d} {σ col : ℤ}
    {z₀ z : Vertex d} (h : PathSiteSpec hd R k σ col z₀ z)
    (hg : z - gadgetShift d R ∈ ambientSites hd (R : ℤ)) :
    z = zeroPad d (col, -halfSide R - 1) := by
  have hm : 2 * halfSide R ≤ R ∧ (R : ℤ) ≤ 2 * halfSide R + 1 := by unfold halfSide; omega
  have hd0 : 0 < d := by omega
  have hd1 : 1 < d := by omega
  obtain ⟨hg01, hg2⟩ := hg
  simp only [Pi.sub_apply, gadgetShift, zeroPad_apply, if_true, one_ne_zero, if_false] at hg01
  rcases h with ⟨⟨i, hi⟩, -⟩ | ⟨-, -, h | h | h | h⟩
  · exfalso
    by_cases hi0 : i.val = 0
    · obtain rfl : i = ⟨0, hd0⟩ := Fin.ext hi0
      omega
    · by_cases hi1 : i.val = 1
      · obtain rfl : i = ⟨1, hd1⟩ := Fin.ext hi1
        omega
      · have := hg2 i (by omega)
        simp only [Pi.sub_apply, gadgetShift, zeroPad_apply, hi0, hi1, if_false] at this
        omega
  · omega
  · omega
  · omega
  · exact h

/-- **The paths of Figure `attach-gadget`.** For `R ≥ 5` and boundary placements `(x, x̃)`,
`(y, ỹ)` with `x ≠ y`: the paths `P₁` (from the low site) and `P₂` (from the high site) are
vertex-disjoint, avoid `Q_{R/2}`, and meet the translated gadget only at its terminals
`s = (-2, -m-1)` and `t = (1, -m-1)` respectively. -/
theorem attachPaths_spec (hd : 2 ≤ d) {R : ℕ} (hR : 5 ≤ R) {x x' y y' : Vertex d}
    (hx : (x, x') ∈ boundaryPairs d R) (hy : (y, y') ∈ boundaryPairs d R) (hxy : x ≠ y) :
    Disjoint (bondSites (lowPathBonds hd R x y)) (bondSites (highPathBonds hd R x y)) ∧
      (∀ z ∈ bondSites (lowPathBonds hd R x y), z ∉ cube d (R / 2) ∧
        (z - gadgetShift d R ∈ ambientSites hd (R : ℤ) → z = zeroPad d (-2, -halfSide R - 1))) ∧
      (∀ z ∈ bondSites (highPathBonds hd R x y), z ∉ cube d (R / 2) ∧
        (z - gadgetShift d R ∈ ambientSites hd (R : ℤ) → z = zeroPad d (1, -halfSide R - 1))) :=
  ⟨attachPaths_disjoint hd hR hx hy hxy,
    fun z hz => ⟨(lowPath_sites hd hR hx hy hxy z hz).not_mem_cube hR,
      (lowPath_sites hd hR hx hy hxy z hz).eq_of_gadget hR⟩,
    fun z hz => ⟨(highPath_sites hd hR hx hy hxy z hz).not_mem_cube hR,
      (highPath_sites hd hR hx hy hxy z hz).eq_of_gadget hR⟩⟩

/-- The terminal `s = (1, 1)` of the gadget, translated by `τ_R`, is `(-2, -m-1)`. -/
theorem gadgetShift_add_source (R : ℕ) :
    gadgetShift d R + zeroPad d (1, 1) = zeroPad d (-2, -halfSide R - 1) := by
  funext i
  simp only [Pi.add_apply, gadgetShift, zeroPad_apply]
  split_ifs <;> omega

/-- The terminal `t = (4, 1)` of the gadget, translated by `τ_R`, is `(1, -m-1)`. -/
theorem gadgetShift_add_target (R : ℕ) :
    gadgetShift d R + zeroPad d (4, 1) = zeroPad d (1, -halfSide R - 1) := by
  funext i
  simp only [Pi.add_apply, gadgetShift, zeroPad_apply]
  split_ifs <;> omega

/-- **The gadget is isolated in `H R x y`**: for `R ≥ 5` it lies in `Q_{R-1}`, and a bond of
`H R x y` at a gadget site other than the terminals is a gadget bond (the paths `P₁`, `P₂` meet the
gadget only at `s` and `t`, `attachPaths_spec`), so both its endpoints are gadget sites. -/
theorem attachBondSet_isolated (hd : 2 ≤ d) {R : ℕ} (hR : 5 ≤ R) {x x' y y' : Vertex d}
    (hx : (x, x') ∈ boundaryPairs d R) (hy : (y, y') ∈ boundaryPairs d R) (hxy : x ≠ y) :
    IsIsolatedGadget hd R (attachBondSet hd R x y) (gadgetShift d R) := by
  obtain ⟨-, hlow, hhigh⟩ := attachPaths_spec hd hR hx hy hxy
  refine ⟨fun g hg => gadget_mem_cube_pred hd (by omega) hg, ?_⟩
  intro e he g hg hs ht hge z hz
  have hgg : gadgetShift d R + g - gadgetShift d R ∈ ambientSites hd (R : ℤ) := by
    rwa [add_sub_cancel_left]
  rcases he with (he | he) | he
  · exact ⟨z - gadgetShift d R, he z hz, by abel⟩
  · have h := (hlow _ ⟨e, he, hge⟩).2 hgg
    rw [← gadgetShift_add_source R] at h
    exact absurd (add_left_cancel h) hs
  · have h := (hhigh _ ⟨e, he, hge⟩).2 hgg
    rw [← gadgetShift_add_target R] at h
    exact absurd (add_left_cancel h) ht

/-- **`step:4.8-attach`, geometry**: for `R ≥ 5` the bond set `H R x y` of Figure `attach-gadget`
lies in `Q_R` and contains the gadget of height `R`, translated by `τ_R`, as an induced subgraph,
and the gadget is isolated in it (inside `Q_{R-1}`, attached at its terminals only). -/
theorem attachGeometryStep (hd : 2 ≤ d) :
    AttachGeometryStep hd (attachBondSet hd) (gadgetShift d) :=
  ⟨5, fun _ hR _ _ _ _ hx hy hxy =>
    ⟨attachBondSet_isGadgetPlacement hd (by omega) hx hy, attachBondSet_isolated hd hR hx hy hxy⟩⟩

/-! ### The paths `P₁`, `P₂` join the boundary sites to the terminals -/

theorem update_add_one (z : Vertex d) (j : Fin d) (v : ℤ) :
    Function.update z j (v + 1) = Function.update z j v + unit j := by
  funext i
  rcases eq_or_ne i j with rfl | hij
  · simp [unit]
  · simp [unit, Function.update_of_ne hij, Pi.single_eq_of_ne hij]

theorem update_adj_update (z : Vertex d) (j : Fin d) (v : ℤ) :
    (nearestNeighborGraph d).Adj (Function.update z j v) (Function.update z j (v + 1)) :=
  ⟨j, Or.inl (update_add_one z j v)⟩

theorem segment_walk_up (z : Vertex d) (j : Fin d) (u : ℤ) : ∀ n : ℕ,
    ∃ W : (nearestNeighborGraph d).Walk (Function.update z j u) (Function.update z j (u + n)),
      ∀ e ∈ W.edges, ∃ v, u ≤ v ∧ v < u + n ∧
        e = s(Function.update z j v, Function.update z j (v + 1))
  | 0 => ⟨SimpleGraph.Walk.nil.copy rfl (by simp), by simp⟩
  | n + 1 => by
    obtain ⟨W, hW⟩ := segment_walk_up z j u n
    refine ⟨(W.concat (update_adj_update z j (u + n))).copy rfl
      (by rw [Nat.cast_succ, add_assoc]), fun e he => ?_⟩
    simp only [SimpleGraph.Walk.edges_copy, SimpleGraph.Walk.edges_concat, List.concat_eq_append,
      List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · obtain ⟨v, h₁, h₂, rfl⟩ := hW e he
      exact ⟨v, h₁, by push_cast; omega, rfl⟩
    · exact ⟨u + n, by omega, by push_cast; omega, rfl⟩

/-- The lattice segment through `z` in the direction `j`, between the values `u` and `w` of the
`j`-th coordinate, is a walk along `segmentBonds z j u w`. -/
theorem segment_walk (z : Vertex d) (j : Fin d) (u w : ℤ) :
    ∃ W : (nearestNeighborGraph d).Walk (Function.update z j u) (Function.update z j w),
      ∀ e ∈ W.edges, ∃ f ∈ segmentBonds z j u w, (f : Sym2 (Vertex d)) = e := by
  rcases le_total u w with h | h
  · obtain ⟨W, hW⟩ := segment_walk_up z j u (w - u).toNat
    have hw : u + ((w - u).toNat : ℤ) = w := by omega
    refine ⟨W.copy rfl (by rw [hw]), fun e he => ?_⟩
    rw [SimpleGraph.Walk.edges_copy] at he
    obtain ⟨v, h₁, h₂, rfl⟩ := hW e he
    exact ⟨bondOfAdjacent (update_adj_update z j v), ⟨v, by omega, by omega, rfl⟩, rfl⟩
  · obtain ⟨W, hW⟩ := segment_walk_up z j w (u - w).toNat
    have hu : w + ((u - w).toNat : ℤ) = u := by omega
    refine ⟨(W.copy rfl (by rw [hu])).reverse, fun e he => ?_⟩
    rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse, SimpleGraph.Walk.edges_copy] at he
    obtain ⟨v, h₁, h₂, rfl⟩ := hW e he
    exact ⟨bondOfAdjacent (update_adj_update z j v), ⟨v, by omega, by omega, rfl⟩, rfl⟩

/-- The corner of the staircase from `a` to `b` after its first `n` legs. -/
def stairCornerAfter (a b : Vertex d) (n : ℕ) : Vertex d := fun i => if i.val < n then b i else a i

theorem stair_walk_aux (a b : Vertex d) : ∀ n : ℕ, n ≤ d →
    ∃ W : (nearestNeighborGraph d).Walk a (stairCornerAfter a b n),
      ∀ e ∈ W.edges, ∃ f ∈ stairBonds a b, (f : Sym2 (Vertex d)) = e
  | 0, _ => ⟨SimpleGraph.Walk.nil.copy rfl (by funext i; simp [stairCornerAfter]), by simp⟩
  | n + 1, hn => by
    obtain ⟨W, hW⟩ := stair_walk_aux a b n (by omega)
    have hnd : n < d := by omega
    have h₁ : Function.update (stairCorner a b ⟨n, hnd⟩) ⟨n, hnd⟩ (a ⟨n, hnd⟩) =
        stairCornerAfter a b n := by
      funext i
      rcases eq_or_ne i ⟨n, hnd⟩ with rfl | hij
      · simp [stairCornerAfter]
      · have : i.val ≠ n := fun h => hij (Fin.ext h)
        rw [Function.update_of_ne hij]
        simp only [stairCorner, stairCornerAfter, Fin.lt_def]
    have h₂ : Function.update (stairCorner a b ⟨n, hnd⟩) ⟨n, hnd⟩ (b ⟨n, hnd⟩) =
        stairCornerAfter a b (n + 1) := by
      funext i
      rcases eq_or_ne i ⟨n, hnd⟩ with rfl | hij
      · simp [stairCornerAfter]
      · have : i.val ≠ n := fun h => hij (Fin.ext h)
        rw [Function.update_of_ne hij]
        simp only [stairCorner, stairCornerAfter, Fin.lt_def]
        split_ifs <;> first | rfl | omega
    set j : Fin d := ⟨n, hnd⟩
    obtain ⟨S, hS⟩ := segment_walk (stairCorner a b j) j (a j) (b j)
    refine ⟨W.append (S.copy h₁ h₂), fun e he => ?_⟩
    rw [SimpleGraph.Walk.edges_append, List.mem_append, SimpleGraph.Walk.edges_copy] at he
    rcases he with he | he
    · exact hW e he
    · obtain ⟨f, hf, rfl⟩ := hS e he
      exact ⟨f, Set.mem_iUnion.mpr ⟨j, hf⟩, rfl⟩

/-- The staircase from `a` to `b` is a walk along `stairBonds a b`. -/
theorem stair_walk (a b : Vertex d) :
    ∃ W : (nearestNeighborGraph d).Walk a b,
      ∀ e ∈ W.edges, ∃ f ∈ stairBonds a b, (f : Sym2 (Vertex d)) = e := by
  obtain ⟨W, hW⟩ := stair_walk_aux a b d le_rfl
  have : stairCornerAfter a b d = b := by funext i; simp [stairCornerAfter, i.isLt]
  exact ⟨W.copy rfl this, by simpa using hW⟩

/-- The polygonal path through the waypoints `a :: l` is a walk along `chainBonds (a :: l)`. -/
theorem chain_walk : ∀ (a : Vertex d) (l : List (Vertex d)),
    ∃ W : (nearestNeighborGraph d).Walk a ((a :: l).getLast (List.cons_ne_nil a l)),
      ∀ e ∈ W.edges, ∃ f ∈ chainBonds (a :: l), (f : Sym2 (Vertex d)) = e
  | a, [] => ⟨SimpleGraph.Walk.nil, by simp⟩
  | a, b :: l => by
    obtain ⟨W, hW⟩ := chain_walk b l
    obtain ⟨S, hS⟩ := stair_walk a b
    refine ⟨(S.append W).copy rfl (by rw [List.getLast_cons_cons]), fun e he => ?_⟩
    rw [SimpleGraph.Walk.edges_copy, SimpleGraph.Walk.edges_append, List.mem_append] at he
    rcases he with he | he
    · obtain ⟨f, hf, rfl⟩ := hS e he
      exact ⟨f, Or.inl hf, rfl⟩
    · obtain ⟨f, hf, rfl⟩ := hW e he
      exact ⟨f, Or.inr hf, rfl⟩

/-- `P₁` contains a lattice path from the low site to the terminal `s = (-2, -m-1)`. -/
theorem lowPath_walk (hd : 2 ≤ d) (R : ℕ) (x y : Vertex d) :
    ∃ W : (nearestNeighborGraph d).Walk (lowSite hd x y) (zeroPad d (-2, -halfSide R - 1)),
      W.IsPath ∧ ∀ e ∈ W.edges, ∃ f ∈ lowPathBonds hd R x y, (f : Sym2 (Vertex d)) = e := by
  obtain ⟨W, hW⟩ := chain_walk (lowSite hd x y) (attachWaypoints R (sepCoord hd x y) (-1) (-2)
    (lowSite hd x y)).tail
  refine ⟨W.bypass, W.bypass_isPath, fun e he => hW e (W.edges_bypass_subset_edges he)⟩

/-- `P₂` contains a lattice path from the high site to the terminal `t = (1, -m-1)`. -/
theorem highPath_walk (hd : 2 ≤ d) (R : ℕ) (x y : Vertex d) :
    ∃ W : (nearestNeighborGraph d).Walk (highSite hd x y) (zeroPad d (1, -halfSide R - 1)),
      W.IsPath ∧ ∀ e ∈ W.edges, ∃ f ∈ highPathBonds hd R x y, (f : Sym2 (Vertex d)) = e := by
  obtain ⟨W, hW⟩ := chain_walk (highSite hd x y) (attachWaypoints R (sepCoord hd x y) 1 1
    (highSite hd x y)).tail
  refine ⟨W.bypass, W.bypass_isPath, fun e he => hW e (W.edges_bypass_subset_edges he)⟩

/-! ### `step:4.8-union`: counting the boundary placements -/

/-- **`step:4.8-union`**: there are at most `2 d 3^{d-1} R^{d-1}` boundary placements `(x, x̃)`
of `Q_R`, `R ≥ 1`. A placement is determined by the coordinate `i` and the direction of
`x̃ - x = ± e_i`, which force `x_i = ± R`, and by the other coordinates of `x`. -/
theorem placementCountStep : PlacementCountStep d := by
  cases d with
  | zero =>
    refine ⟨1, one_pos, fun R _ => ?_⟩
    have h : boundaryPairs 0 R = ∅ := by
      ext z
      simp only [boundaryPairs, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨-, h, -⟩
      exact h (fun i => i.elim0)
    simp [h]
  | succ n =>
    refine ⟨2 * (n + 1) * 3 ^ n, by positivity, fun R hR => ?_⟩
    set D : Finset (Fin (n + 1) × Bool × (Fin n → ℤ)) :=
      Finset.univ ×ˢ Finset.univ ×ˢ Fintype.piFinset (fun _ => Finset.Icc (-(R : ℤ)) R)
    set g : Fin (n + 1) × Bool × (Fin n → ℤ) → Vertex (n + 1) × Vertex (n + 1) := fun p =>
      (Fin.insertNth p.1 (if p.2.1 then (R : ℤ) else -R) p.2.2,
        Fin.insertNth p.1 (if p.2.1 then (R : ℤ) + 1 else -R - 1) p.2.2)
    have hsub : boundaryPairs (n + 1) R ⊆ ↑(D.image g) := by
      rintro ⟨x, x'⟩ ⟨hx, hx', i, hadj⟩
      dsimp only at hx hx' hadj
      have hout : ∀ j, j ≠ i → x' j = x j := by
        intro j hj
        rcases hadj with rfl | rfl <;> simp [unit, hj]
      have hxi : ¬ |x' i| ≤ R := by
        intro h
        apply hx'
        intro j
        by_cases hj : j = i
        · subst hj; exact h
        · rw [hout j hj]; exact hx j
      rw [abs_le] at hxi
      have hxi' := abs_le.mp (hx i)
      have hrest : Fin.removeNth i x' = Fin.removeNth i x := by
        funext j
        exact hout _ (Fin.succAbove_ne i j)
      have hmem : Fin.removeNth i x ∈ Fintype.piFinset (fun _ => Finset.Icc (-(R : ℤ)) R) := by
        rw [Fintype.mem_piFinset]
        intro j
        exact Finset.mem_Icc.mpr (abs_le.mp (hx _))
      rcases hadj with h | h
      · have hx'i : x' i = x i + 1 := by rw [h]; simp [unit]
        have h₁ : x i = R := by omega
        have h₂ : x' i = R + 1 := by omega
        refine Finset.mem_image.mpr ⟨(i, true, Fin.removeNth i x), by simp [D, hmem], ?_⟩
        refine Prod.ext ?_ ?_
        · simp only [g, if_true]
          rw [← h₁]; exact Fin.insertNth_self_removeNth i x
        · simp only [g, if_true]
          rw [← hrest, ← h₂]; exact Fin.insertNth_self_removeNth i x'
      · have hx'i : x i = x' i + 1 := by rw [h]; simp [unit]
        have h₁ : x i = -R := by omega
        have h₂ : x' i = -R - 1 := by omega
        refine Finset.mem_image.mpr ⟨(i, false, Fin.removeNth i x), by simp [D, hmem], ?_⟩
        refine Prod.ext ?_ ?_
        · simp only [g, Bool.false_eq_true, if_false]
          rw [← h₁]; exact Fin.insertNth_self_removeNth i x
        · simp only [g, Bool.false_eq_true, if_false]
          rw [← hrest, ← h₂]; exact Fin.insertNth_self_removeNth i x'
    refine ⟨(D.image g).finite_toSet.subset hsub, ?_⟩
    have hcard : (boundaryPairs (n + 1) R).ncard ≤ D.card :=
      (Set.ncard_le_ncard hsub (Finset.finite_toSet _)).trans
        ((Set.ncard_coe_finset _).le.trans Finset.card_image_le)
    have hD : D.card = (n + 1) * (2 * (2 * R + 1) ^ n) := by
      have h₁ : ((R : ℤ) + 1 - -(R : ℤ)).toNat = 2 * R + 1 := by omega
      simp only [D, Finset.card_product, Finset.card_univ, Fintype.card_fin, Fintype.card_bool,
        Fintype.card_piFinset, Int.card_Icc, Finset.prod_const, h₁]
    have hR' : (1 : ℝ) ≤ R := by exact_mod_cast hR
    calc ((boundaryPairs (n + 1) R).ncard : ℝ) ≤ (D.card : ℝ) := by exact_mod_cast hcard
      _ = ((n : ℝ) + 1) * (2 * (2 * (R : ℝ) + 1) ^ n) := by rw [hD]; push_cast; ring
      _ ≤ ((n : ℝ) + 1) * (2 * (3 * (R : ℝ)) ^ n) := by gcongr; linarith
      _ = 2 * ((n : ℝ) + 1) * 3 ^ n * (R : ℝ) ^ (n + 1 - 1) := by
        rw [Nat.add_sub_cancel, mul_pow]; ring

end Rigidity.Proofs.S4
