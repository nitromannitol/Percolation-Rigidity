import Rigidity.Proofs.Section5.JordanLoop

/-! # Unions of lattice cells: interior, frontier and centres

The cells are the closed squares `Cell c` of side `1 / 2` centred at `c / 2`, `c ∈ ℤ²`, of
`Rigidity.Proofs.Section5.JordanLoop`. For a finite set `S` of cells and the union `cellUnion S`
of its cells:

* a point lies in the interior of `cellUnion S` if and only if every cell containing it is in `S`
  (`mem_interior_cellUnion`);
* the closure of this interior is `cellUnion S`, and its frontier is the union `bdry S` of the
  sides between a cell of `S` and a cell not in `S` (`frontier_interior_cellUnion`);
* the segment between the centres of two adjacent cells which are both in `S` or both outside
  `S` avoids `bdry S` (`segment_ctr_subset`).
-/

open Set Filter Topology Function

namespace Rigidity.Proofs.Topology.Polyomino

open Rigidity.Proofs.Section5.JordanLoop

/-- The centre `c / 2` of the cell `c`. -/
noncomputable def ctr (c : ℤ × ℤ) : E2 := pt (c.1 / 2) (c.2 / 2)

/-- The open cell `c`: the interior of `Cell c`. -/
def OpenCell (c : ℤ × ℤ) : Set E2 := {p | |p 0 - c.1 / 2| < 1 / 4 ∧ |p 1 - c.2 / 2| < 1 / 4}

/-- The union of the cells of `S`. -/
def cellUnion (S : Set (ℤ × ℤ)) : Set E2 := ⋃ c ∈ S, Cell c

/-- The union of the sides between a cell of `S` and a cell not in `S`. -/
def bdry (S : Set (ℤ × ℤ)) : Set E2 :=
  {p | ∃ c ∈ S, ∃ n : Dir, c + n.v ∉ S ∧ p ∈ Cell c ∩ Cell (c + n.v)}

theorem isOpen_openCell (c : ℤ × ℤ) : IsOpen (OpenCell c) := by
  have : OpenCell c = {p : E2 | |p 0 - c.1 / 2| < 1 / 4} ∩ {p : E2 | |p 1 - c.2 / 2| < 1 / 4} :=
    rfl
  rw [this]
  exact (isOpen_lt (((EuclideanSpace.proj (0 : Fin 2) : E2 →L[ℝ] ℝ).continuous.sub
    continuous_const).abs) continuous_const).inter (isOpen_lt (((EuclideanSpace.proj (1 : Fin 2) :
      E2 →L[ℝ] ℝ).continuous.sub continuous_const).abs) continuous_const)

theorem openCell_subset_cell (c : ℤ × ℤ) : OpenCell c ⊆ Cell c :=
  fun _ hp => ⟨hp.1.le, hp.2.le⟩

theorem ctr_mem_openCell (c : ℤ × ℤ) : ctr c ∈ OpenCell c := by
  norm_num [OpenCell, ctr]

theorem isPreconnected_openCell (c : ℤ × ℤ) : IsPreconnected (OpenCell c) := by
  refine Convex.isPreconnected fun p hp q hq a b ha hb hab => ?_
  have key : ∀ x y m : ℝ, |x - m| < 1 / 4 → |y - m| < 1 / 4 → |a * x + b * y - m| < 1 / 4 := by
    intro x y m hx hy
    have : a * x + b * y - m = a * (x - m) + b * (y - m) := by
      linear_combination m * hab
    rw [this]
    calc |a * (x - m) + b * (y - m)| ≤ |a * (x - m)| + |b * (y - m)| := abs_add_le _ _
      _ = a * |x - m| + b * |y - m| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * max |x - m| |y - m| + b * max |x - m| |y - m| :=
          add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
            (mul_le_mul_of_nonneg_left (le_max_right _ _) hb)
      _ = max |x - m| |y - m| := by rw [← add_mul, hab, one_mul]
      _ < 1 / 4 := max_lt hx hy
  exact ⟨by simpa using key _ _ _ hp.1 hq.1, by simpa using key _ _ _ hp.2 hq.2⟩

/-- Two integers `a, b` with `|x - a / 2| < 1 / 4` and `|x - b / 2| ≤ 1 / 4` are equal. -/
theorem int_eq_of_close {a b : ℤ} {x : ℝ} (ha : |x - a / 2| < 1 / 4) (hb : |x - b / 2| ≤ 1 / 4) :
    a = b := by
  rw [abs_lt] at ha
  rw [abs_le] at hb
  have h1 : ((a - b : ℤ) : ℝ) < 1 := by push_cast; linarith
  have h2 : (-1 : ℝ) < ((a - b : ℤ) : ℝ) := by push_cast; linarith
  have h3 : a - b < 1 := by exact_mod_cast h1
  have h4 : -1 < a - b := by exact_mod_cast h2
  omega

/-- A point of the open cell `c` lies in no other cell. -/
theorem eq_of_mem_openCell {c d : ℤ × ℤ} {p : E2} (hc : p ∈ OpenCell c) (hd : p ∈ Cell d) :
    d = c :=
  Prod.ext (int_eq_of_close hc.1 hd.1).symm (int_eq_of_close hc.2 hd.2).symm

/-- Moving a point of `Cell c` towards the centre puts it in the open cell. -/
theorem openCell_of_shrink {c : ℤ × ℤ} {p : E2} (hp : p ∈ Cell c) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t ≤ 1) : p + t • (ctr c - p) ∈ OpenCell c := by
  obtain ⟨h0, h1⟩ := hp
  have key : ∀ x m : ℝ, |x - m| ≤ 1 / 4 → |x + t * (m - x) - m| < 1 / 4 := by
    intro x m hx
    have : x + t * (m - x) - m = (1 - t) * (x - m) := by ring
    rw [this, abs_mul, abs_of_nonneg (by linarith)]
    nlinarith [abs_nonneg (x - m), mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 hx)]
  refine ⟨?_, ?_⟩
  · have := key _ _ h0
    simpa [ctr] using this
  · have := key _ _ h1
    simpa [ctr] using this

/-- Every point of a closed cell is a limit of points of the open cell. -/
theorem mem_closure_openCell {c : ℤ × ℤ} {p : E2} (hp : p ∈ Cell c) :
    p ∈ closure (OpenCell c) := by
  have hf : Continuous fun t : ℝ => p + t • (ctr c - p) := by fun_prop
  have hlim : Tendsto (fun t : ℝ => p + t • (ctr c - p)) (𝓝[>] 0) (𝓝 p) := by
    have := hf.tendsto 0
    simp only [zero_smul, add_zero] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  refine mem_closure_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
  exact openCell_of_shrink hp ht.1 ht.2.le

/-- One coordinate: near `x`, every half-integer interval `[m/2 - 1/4, m/2 + 1/4]` containing a
point also contains `x`. -/
theorem exists_nhds_1d (x : ℝ) : ∃ δ > 0, ∀ y, |y - x| < δ → ∀ m : ℤ,
    |y - m / 2| ≤ 1 / 4 → |x - m / 2| ≤ 1 / 4 := by
  set m₀ := ⌊2 * x + 1 / 2⌋ with hm₀
  have h1 := Int.floor_le (2 * x + 1 / 2)
  have h2 := Int.lt_floor_add_one (2 * x + 1 / 2)
  rw [← hm₀] at h1 h2
  rcases lt_or_eq_of_le h1 with h | h
  · refine ⟨1 / 4 - |x - m₀ / 2|, ?_, fun y hy m hm => ?_⟩
    · show 0 < 1 / 4 - |x - m₀ / 2|
      rw [sub_pos, abs_lt]; constructor <;> linarith
    · have hmm : |(m : ℝ) / 2 - m₀ / 2| < 1 / 2 := by
        have e1 := abs_sub_le ((m : ℝ) / 2) y (m₀ / 2)
        have e2 := abs_sub_le y x (m₀ / 2)
        rw [abs_sub_comm] at hm
        linarith
      rw [abs_lt] at hmm
      have a1 : ((m - m₀ : ℤ) : ℝ) < 1 := by push_cast; linarith
      have a2 : (-1 : ℝ) < ((m - m₀ : ℤ) : ℝ) := by push_cast; linarith
      have b1 : m - m₀ < 1 := by exact_mod_cast a1
      have b2 : -1 < m - m₀ := by exact_mod_cast a2
      rw [show m = m₀ by omega, abs_le]
      constructor <;> linarith
  · refine ⟨1 / 4, by norm_num, fun y hy m hm => ?_⟩
    rw [abs_lt] at hy
    rw [abs_le] at hm
    have a1 : ((m - m₀ : ℤ) : ℝ) < 1 := by push_cast; linarith
    have a2 : (-2 : ℝ) < ((m - m₀ : ℤ) : ℝ) := by push_cast; linarith
    have b1 : m - m₀ < 1 := by exact_mod_cast a1
    have b2 : -2 < m - m₀ := by exact_mod_cast a2
    rcases (show m = m₀ ∨ m = m₀ - 1 by omega) with rfl | rfl
    · rw [abs_le]; constructor <;> linarith
    · rw [abs_le]; push_cast; constructor <;> linarith

/-- Near `p`, every cell containing a point contains `p`. -/
theorem exists_ball_cell_mem (p : E2) : ∃ δ > 0, ∀ q ∈ Metric.ball p δ, ∀ d : ℤ × ℤ,
    q ∈ Cell d → p ∈ Cell d := by
  obtain ⟨δ₀, hδ₀, h₀⟩ := exists_nhds_1d (p 0)
  obtain ⟨δ₁, hδ₁, h₁⟩ := exists_nhds_1d (p 1)
  refine ⟨min δ₀ δ₁, lt_min hδ₀ hδ₁, fun q hq d hd => ?_⟩
  have hd' : ∀ j, |q j - p j| < min δ₀ δ₁ := fun j => by
    rw [Metric.mem_ball] at hq
    have := (PiLp.dist_apply_le q p j).trans_lt hq
    rwa [Real.dist_eq] at this
  exact ⟨h₀ _ ((hd' 0).trans_le (min_le_left _ _)) _ hd.1,
    h₁ _ ((hd' 1).trans_le (min_le_right _ _)) _ hd.2⟩

theorem exists_mem_cell (p : E2) : ∃ c, p ∈ Cell c := by
  obtain ⟨δ, hδ, h⟩ := exists_cell_cover p
  obtain ⟨c, hc, -⟩ := h p (Metric.mem_ball_self hδ)
  exact ⟨c, hc⟩

variable {S : Set (ℤ × ℤ)}

theorem isClosed_cellUnion (hS : S.Finite) : IsClosed (cellUnion S) :=
  hS.isClosed_biUnion fun c _ => isClosed_cell c

theorem openCell_subset_interior {c : ℤ × ℤ} (hc : c ∈ S) :
    OpenCell c ⊆ interior (cellUnion S) :=
  interior_maximal (fun _ hp => mem_iUnion₂.2 ⟨c, hc, openCell_subset_cell c hp⟩)
    (isOpen_openCell c)

/-- A cell not in `S` does not meet the interior of `cellUnion S`. -/
theorem notMem_interior {c : ℤ × ℤ} (hc : c ∉ S) {p : E2} (hp : p ∈ Cell c) :
    p ∉ interior (cellUnion S) := by
  rw [interior_eq_compl_closure_compl, notMem_compl_iff]
  refine closure_mono (fun q hq => ?_) (mem_closure_openCell hp)
  simp only [cellUnion, mem_compl_iff, mem_iUnion₂, not_exists]
  intro d hd hqd
  exact hc (eq_of_mem_openCell hq hqd ▸ hd)

theorem mem_interior_cellUnion {p : E2} :
    p ∈ interior (cellUnion S) ↔ ∀ d, p ∈ Cell d → d ∈ S := by
  constructor
  · intro hp d hd
    by_contra h
    exact notMem_interior h hd hp
  · intro h
    obtain ⟨δ, hδ, hb⟩ := exists_ball_cell_mem p
    refine mem_interior.2 ⟨Metric.ball p δ, fun q hq => ?_, Metric.isOpen_ball,
      Metric.mem_ball_self hδ⟩
    obtain ⟨d, hd⟩ := exists_mem_cell q
    exact mem_iUnion₂.2 ⟨d, h d (hb q hq d hd), hd⟩

theorem closure_interior_cellUnion (hS : S.Finite) :
    closure (interior (cellUnion S)) = cellUnion S := by
  refine Subset.antisymm ((closure_mono interior_subset).trans
    (isClosed_cellUnion hS).closure_subset) ?_
  exact iUnion₂_subset fun c hc p hp =>
    closure_mono (openCell_subset_interior hc) (mem_closure_openCell hp)

theorem exists_dir_of_fst_eq {a b : ℤ × ℤ} (h1 : a.1 = b.1) (h2 : |a.2 - b.2| ≤ 1)
    (hab : a ≠ b) : ∃ n : Dir, b = a + n.v := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  simp only at h1 h2
  subst h1
  rw [abs_le] at h2
  rcases (show b2 = a2 + 1 ∨ b2 = a2 - 1 ∨ b2 = a2 by omega) with rfl | rfl | rfl
  · exact ⟨.N, by ext <;> simp [Dir.v]⟩
  · exact ⟨.S, by ext <;> simp [Dir.v]; ring⟩
  · exact absurd rfl hab

theorem exists_dir_of_snd_eq {a b : ℤ × ℤ} (h1 : a.2 = b.2) (h2 : |a.1 - b.1| ≤ 1)
    (hab : a ≠ b) : ∃ n : Dir, b = a + n.v := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  simp only at h1 h2
  subst h1
  rw [abs_le] at h2
  rcases (show b1 = a1 + 1 ∨ b1 = a1 - 1 ∨ b1 = a1 by omega) with rfl | rfl | rfl
  · exact ⟨.E, by ext <;> simp [Dir.v]⟩
  · exact ⟨.W, by ext <;> simp [Dir.v]; ring⟩
  · exact absurd rfl hab

/-- A point lying in a cell of `S` and in a cell not in `S` lies on a side between a cell of `S`
and a cell not in `S`. -/
theorem exists_side {c d : ℤ × ℤ} (hc : c ∈ S) (hd : d ∉ S) {p : E2} (hpc : p ∈ Cell c)
    (hpd : p ∈ Cell d) : p ∈ bdry S := by
  have hcl := cell_coord_close hpc hpd
  have hpe : p ∈ Cell (d.1, c.2) := ⟨hpd.1, hpc.2⟩
  by_cases he : (d.1, c.2) ∈ S
  · obtain ⟨n, hn⟩ := exists_dir_of_fst_eq (a := (d.1, c.2)) (b := d) rfl hcl.2
      (fun h => hd (h ▸ he))
    refine ⟨_, he, n, ?_, hpe, ?_⟩
    · rw [← hn]; exact hd
    · rw [← hn]; exact hpd
  · obtain ⟨n, hn⟩ := exists_dir_of_snd_eq (a := c) (b := (d.1, c.2)) rfl hcl.1
      (fun h => he (h ▸ hc))
    refine ⟨c, hc, n, ?_, hpc, ?_⟩
    · rw [← hn]; exact he
    · rw [← hn]; exact hpe

/-- The frontier of the interior of a finite union of cells is the union of the sides between a
cell of `S` and a cell not in `S`. -/
theorem frontier_interior_cellUnion (hS : S.Finite) :
    frontier (interior (cellUnion S)) = bdry S := by
  rw [frontier, closure_interior_cellUnion hS, interior_interior]
  ext p
  rw [Set.mem_sdiff, mem_interior_cellUnion]
  push Not
  constructor
  · rintro ⟨hpU, d, hpd, hdS⟩
    obtain ⟨c, hc, hpc⟩ := mem_iUnion₂.1 hpU
    exact exists_side hc hdS hpc hpd
  · rintro ⟨c, hc, n, hn, hpc, hpn⟩
    exact ⟨mem_iUnion₂.2 ⟨c, hc, hpc⟩, c + n.v, hpn, hn⟩

theorem bdry_subset_cellUnion : bdry S ⊆ cellUnion S := by
  rintro p ⟨c, hc, -, -, hpc, -⟩
  exact mem_iUnion₂.2 ⟨c, hc, hpc⟩

/-- The cells containing a point of the segment between the centres of two adjacent cells are
these two cells. -/
theorem cell_of_mem_segment_ctr {c : ℤ × ℤ} {n : Dir} {q : E2}
    (hq : q ∈ segment ℝ (ctr c) (ctr (c + n.v))) {d : ℤ × ℤ} (hd : q ∈ Cell d) :
    d = c ∨ d = c + n.v := by
  obtain ⟨t, ⟨ht0, ht1⟩, hqt⟩ := coords_of_mem_segment hq
  have e0 : q 0 = c.1 / 2 + t * ((n.v.1 : ℝ) / 2) := by
    rw [hqt 0]; simp only [ctr, pt_zero, Prod.fst_add]; push_cast; ring
  have e1 : q 1 = c.2 / 2 + t * ((n.v.2 : ℝ) / 2) := by
    rw [hqt 1]; simp only [ctr, pt_one, Prod.snd_add]; push_cast; ring
  obtain ⟨hd1, hd2⟩ := hd
  rw [e0, abs_le] at hd1
  rw [e1, abs_le] at hd2
  obtain ⟨c1, c2⟩ := c
  obtain ⟨d1, d2⟩ := d
  cases n <;> simp only [Dir.v, Prod.mk_add_mk, Prod.mk.injEq] at hd1 hd2 ⊢ <;>
    push_cast at hd1 hd2
  · have a1 : ((d1 - c1 : ℤ) : ℝ) < 2 := by push_cast; linarith
    have a2 : (-1 : ℝ) < ((d1 - c1 : ℤ) : ℝ) := by push_cast; linarith
    have a3 : ((d2 - c2 : ℤ) : ℝ) < 1 := by push_cast; linarith
    have a4 : (-1 : ℝ) < ((d2 - c2 : ℤ) : ℝ) := by push_cast; linarith
    have b1 : d1 - c1 < 2 := by exact_mod_cast a1
    have b2 : -1 < d1 - c1 := by exact_mod_cast a2
    have b3 : d2 - c2 < 1 := by exact_mod_cast a3
    have b4 : -1 < d2 - c2 := by exact_mod_cast a4
    omega
  · have a1 : ((d1 - c1 : ℤ) : ℝ) < 1 := by push_cast; linarith
    have a2 : (-1 : ℝ) < ((d1 - c1 : ℤ) : ℝ) := by push_cast; linarith
    have a3 : ((d2 - c2 : ℤ) : ℝ) < 2 := by push_cast; linarith
    have a4 : (-1 : ℝ) < ((d2 - c2 : ℤ) : ℝ) := by push_cast; linarith
    have b1 : d1 - c1 < 1 := by exact_mod_cast a1
    have b2 : -1 < d1 - c1 := by exact_mod_cast a2
    have b3 : d2 - c2 < 2 := by exact_mod_cast a3
    have b4 : -1 < d2 - c2 := by exact_mod_cast a4
    omega
  · have a1 : ((d1 - c1 : ℤ) : ℝ) < 1 := by push_cast; linarith
    have a2 : (-2 : ℝ) < ((d1 - c1 : ℤ) : ℝ) := by push_cast; linarith
    have a3 : ((d2 - c2 : ℤ) : ℝ) < 1 := by push_cast; linarith
    have a4 : (-1 : ℝ) < ((d2 - c2 : ℤ) : ℝ) := by push_cast; linarith
    have b1 : d1 - c1 < 1 := by exact_mod_cast a1
    have b2 : -2 < d1 - c1 := by exact_mod_cast a2
    have b3 : d2 - c2 < 1 := by exact_mod_cast a3
    have b4 : -1 < d2 - c2 := by exact_mod_cast a4
    omega
  · have a1 : ((d1 - c1 : ℤ) : ℝ) < 1 := by push_cast; linarith
    have a2 : (-1 : ℝ) < ((d1 - c1 : ℤ) : ℝ) := by push_cast; linarith
    have a3 : ((d2 - c2 : ℤ) : ℝ) < 1 := by push_cast; linarith
    have a4 : (-2 : ℝ) < ((d2 - c2 : ℤ) : ℝ) := by push_cast; linarith
    have b1 : d1 - c1 < 1 := by exact_mod_cast a1
    have b2 : -1 < d1 - c1 := by exact_mod_cast a2
    have b3 : d2 - c2 < 1 := by exact_mod_cast a3
    have b4 : -2 < d2 - c2 := by exact_mod_cast a4
    omega

theorem add_v_ne (c : ℤ × ℤ) (n : Dir) : c + n.v ≠ c := by
  obtain ⟨c1, c2⟩ := c
  cases n <;> simp [Dir.v]

/-- The segment between the centres of two adjacent cells which are both in `S` or both outside
`S` avoids `bdry S`. -/
theorem segment_ctr_subset {c : ℤ × ℤ} {n : Dir} (h : c ∈ S ↔ c + n.v ∈ S) :
    segment ℝ (ctr c) (ctr (c + n.v)) ⊆ (bdry S)ᶜ := by
  rintro q hq ⟨c', hc', n', hn', hq1, hq2⟩
  rcases cell_of_mem_segment_ctr hq hq1 with rfl | e1 <;>
    rcases cell_of_mem_segment_ctr hq hq2 with e2 | e2
  · exact add_v_ne _ _ e2
  · exact hn' (e2 ▸ h.1 hc')
  · rw [e1] at hc'
    exact hn' (e2 ▸ h.2 hc')
  · exact add_v_ne c' n' (e2.trans e1.symm)

/-- The centres of two adjacent cells which are both in `S` or both outside `S` lie in the same
component of the complement of any subset of `bdry S`. -/
theorem ctr_mem_connectedComponentIn {J : Set E2} (hJ : J ⊆ bdry S) {c : ℤ × ℤ} {n : Dir}
    (h : c ∈ S ↔ c + n.v ∈ S) : ctr (c + n.v) ∈ connectedComponentIn Jᶜ (ctr c) :=
  (convex_segment _ _).isPreconnected.subset_connectedComponentIn (left_mem_segment ℝ _ _)
    ((segment_ctr_subset h).trans (compl_subset_compl.2 hJ)) (right_mem_segment ℝ _ _)

/-- No checkerboard corner: if two diagonally adjacent cells are both in `S` or both outside `S`,
and so are the two other cells at their common corner, then all four are in `S` or all four are
outside `S`. -/
def NoChecker (S : Set (ℤ × ℤ)) : Prop :=
  ∀ c d : ℤ × ℤ, |c.1 - d.1| = 1 → |c.2 - d.2| = 1 → (c ∈ S ↔ d ∈ S) →
    ((d.1, c.2) ∈ S ↔ (c.1, d.2) ∈ S) → (c ∈ S ↔ (d.1, c.2) ∈ S)

theorem ctr_notMem_bdry (c : ℤ × ℤ) : ctr c ∉ bdry S := by
  rintro ⟨c', -, n', -, h1, h2⟩
  have e1 := eq_of_mem_openCell (ctr_mem_openCell c) h1
  have e2 := eq_of_mem_openCell (ctr_mem_openCell c) h2
  exact add_v_ne c' n' (e2.trans e1.symm)

/-- Two cells in the same row or column at distance at most one, both in `S` or both outside
`S`: their centres lie in the same component of the complement of any subset of `bdry S`. -/
theorem ctr_mem_of_line {J : Set E2} (hJ : J ⊆ bdry S) {a b : ℤ × ℤ} (hab : a ∈ S ↔ b ∈ S)
    (h : (a.1 = b.1 ∧ |a.2 - b.2| ≤ 1) ∨ (a.2 = b.2 ∧ |a.1 - b.1| ≤ 1)) :
    ctr b ∈ connectedComponentIn Jᶜ (ctr a) := by
  by_cases he : a = b
  · subst he
    exact mem_connectedComponentIn fun h => ctr_notMem_bdry a (hJ h)
  · obtain ⟨n, rfl⟩ : ∃ n : Dir, b = a + n.v := by
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact exists_dir_of_fst_eq h1 h2 he
      · exact exists_dir_of_snd_eq h1 h2 he
    exact ctr_mem_connectedComponentIn hJ hab

/-- Without checkerboard corners, two cells with a common point, both in `S` or both outside
`S`, have their centres in the same component of the complement of any subset of `bdry S`. -/
theorem ctr_mem_of_cells (hNC : NoChecker S) {J : Set E2} (hJ : J ⊆ bdry S) {c d : ℤ × ℤ}
    (hcd : c ∈ S ↔ d ∈ S) {p : E2} (hpc : p ∈ Cell c) (hpd : p ∈ Cell d) :
    ctr d ∈ connectedComponentIn Jᶜ (ctr c) := by
  obtain ⟨h1, h2⟩ := cell_coord_close hpc hpd
  have trans : ∀ e : ℤ × ℤ, ctr e ∈ connectedComponentIn Jᶜ (ctr c) →
      ctr d ∈ connectedComponentIn Jᶜ (ctr e) → ctr d ∈ connectedComponentIn Jᶜ (ctr c) := by
    intro e he hd
    rw [connectedComponentIn_eq he]
    exact hd
  by_cases he : c ∈ S ↔ (d.1, c.2) ∈ S
  · exact trans (d.1, c.2) (ctr_mem_of_line hJ he (Or.inr ⟨rfl, h1⟩))
      (ctr_mem_of_line hJ (he.symm.trans hcd) (Or.inl ⟨rfl, h2⟩))
  by_cases hf : c ∈ S ↔ (c.1, d.2) ∈ S
  · exact trans (c.1, d.2) (ctr_mem_of_line hJ hf (Or.inl ⟨rfl, h2⟩))
      (ctr_mem_of_line hJ (hf.symm.trans hcd) (Or.inr ⟨rfl, h1⟩))
  exfalso
  have hd1 : c.1 ≠ d.1 := fun h => he (by rw [show (d.1, c.2) = c from Prod.ext h.symm rfl])
  have hd2 : c.2 ≠ d.2 := fun h => hf (by rw [show (c.1, d.2) = c from Prod.ext rfl h.symm])
  have a1 : |c.1 - d.1| = 1 := by
    rw [abs_le] at h1; rw [abs_eq (by norm_num)]; omega
  have a2 : |c.2 - d.2| = 1 := by
    rw [abs_le] at h2; rw [abs_eq (by norm_num)]; omega
  exact he (hNC c d a1 a2 hcd (by tauto))

end Rigidity.Proofs.Topology.Polyomino
