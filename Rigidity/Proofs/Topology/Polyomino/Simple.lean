import Rigidity.Proofs.Topology.Polyomino.Cells
import Rigidity.Draft.Section2Polyomino

/-! # Simple boundary points of unions of cells

A boundary point `x` of `Ω` near which `Ω` splits into two disjoint open pieces, both reached by a
sequence of `Ω` converging to `x`, is not simple (`not_simple_of_split`): a curve of `Ω` ending at
`x` eventually stays in one piece. At a checkerboard corner of a union of cells (two diagonal cells
in `S`, the two others not), the interior of the union near the corner is the union of the two
open quarter discs of the cells of `S`; hence, if every boundary point is simple, there is no
checkerboard corner (`noChecker_of_simple`). Simple boundary points are preserved by
homeomorphisms (`IsSimpleBoundaryPoint.of_homeomorph`).
-/

open Set Filter Topology Function

namespace Rigidity.Proofs.Topology.Polyomino

open Rigidity.Proofs.Section5.JordanLoop Rigidity.Section2

/-- A boundary point near which `Ω` splits into two disjoint open pieces visited alternately by a
sequence of `Ω` converging to it is not simple. -/
theorem not_simple_of_split {Ω : Set E2} {x : E2} (hx : x ∉ Ω) {r : ℝ} (hr : 0 < r)
    {P N : Set E2} (hPo : IsOpen P) (hNo : IsOpen N) (hPN : Disjoint P N)
    (hsplit : Ω ∩ Metric.ball x r ⊆ P ∪ N) {u : ℕ → E2} (hu : ∀ n, u n ∈ Ω)
    (hlim : Tendsto u atTop (𝓝 x)) (hP : ∀ k, u (2 * k) ∈ P) (hN : ∀ k, u (2 * k + 1) ∈ N) :
    ¬ IsSimpleBoundaryPoint Ω x := by
  intro hs
  obtain ⟨γ, hγc, hγΩ, hγx, t, ht, ht0, ht1, hγt⟩ := hs u hu hlim
  have hev : {s | γ s ∈ Metric.ball x r} ∈ 𝓝[<] (1 : ℝ) := hγx (Metric.ball_mem_nhds x hr)
  obtain ⟨a, ha1, hasub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 hev
  have htpos : ∀ n, 0 < t n := fun n => ht0.trans_le (ht.monotone (Nat.zero_le n))
  have htend : ∃ n₀, a < t n₀ := by
    by_contra hcon
    push Not at hcon
    have hbdd : BddAbove (range t) := ⟨a, by rintro _ ⟨n, rfl⟩; exact hcon n⟩
    have hL := tendsto_atTop_ciSup ht.monotone hbdd
    have hLa : (⨆ n, t n) ≤ a := ciSup_le hcon
    have hLmem : (⨆ n, t n) ∈ Ico (0 : ℝ) 1 :=
      ⟨(htpos 0).le.trans (le_ciSup hbdd 0), hLa.trans_lt ha1⟩
    have h1 : Tendsto (fun n => γ (t n)) atTop (𝓝 (γ (⨆ n, t n))) :=
      (hγc _ hLmem).tendsto.comp (tendsto_nhdsWithin_iff.2
        ⟨hL, Eventually.of_forall fun n => ⟨(htpos n).le, ht1 n⟩⟩)
    have h2 : Tendsto (fun n => γ (t n)) atTop (𝓝 x) := by
      have : (fun n => γ (t n)) = u := funext hγt
      rw [this]
      exact hlim
    exact hx (tendsto_nhds_unique h1 h2 ▸ hγΩ hLmem)
  obtain ⟨n₀, hn₀⟩ := htend
  have himg : γ '' Ico (t n₀) 1 ⊆ P ∪ N := by
    rintro _ ⟨s, hs, rfl⟩
    exact hsplit ⟨hγΩ ⟨(htpos n₀).le.trans hs.1, hs.2⟩, hasub ⟨hn₀.trans_le hs.1, hs.2⟩⟩
  have hpre : IsPreconnected (γ '' Ico (t n₀) 1) :=
    isPreconnected_Ico.image γ (hγc.mono fun s hs => ⟨(htpos n₀).le.trans hs.1, hs.2⟩)
  have hmem : ∀ n, n₀ ≤ n → u n ∈ γ '' Ico (t n₀) 1 := fun n hn =>
    ⟨t n, ⟨ht.monotone hn, ht1 n⟩, hγt n⟩
  rcases hpre.subset_or_subset hPo hNo hPN himg with h | h
  · exact Set.disjoint_left.1 hPN (h (hmem (2 * n₀ + 1) (by omega))) (hN n₀)
  · exact Set.disjoint_left.1 hPN (hP n₀) (h (hmem (2 * n₀) (by omega)))

/-- Simple boundary points are preserved by homeomorphisms. -/
theorem IsSimpleBoundaryPoint.of_homeomorph (h : E2 ≃ₜ E2) {Ω : Set E2} {x : E2}
    (hs : IsSimpleBoundaryPoint (h '' Ω) (h x)) : IsSimpleBoundaryPoint Ω x := by
  intro u hu hlim
  obtain ⟨γ, hγc, hγΩ, hγx, t, ht, ht0, ht1, hγt⟩ :=
    hs (fun n => h (u n)) (fun n => mem_image_of_mem h (hu n))
      ((h.continuous.tendsto x).comp hlim)
  refine ⟨fun s => h.symm (γ s), h.symm.continuous.comp_continuousOn hγc, fun s hs' => ?_, ?_,
    t, ht, ht0, ht1, fun n => by simp [hγt]⟩
  · obtain ⟨y, hy, hy'⟩ := hγΩ hs'
    simp only
    rw [← hy', Homeomorph.symm_apply_apply]
    exact hy
  · have := (h.symm.continuous.tendsto (h x)).comp hγx
    rw [Homeomorph.symm_apply_apply] at this
    exact this

/-- One coordinate at a corner: on the side of `c` of the corner `(c + d) / 4`, within `1 / 4`,
a point lies in the column of `c`. -/
theorem coord_near_corner {c d : ℤ} (hcd : |c - d| = 1) {y x : ℝ} (hx : x = (c + d) / 4)
    (hy : |y - x| < 1 / 4) (hA : (y - x) * (d - c) ≤ 0) : |y - c / 2| ≤ 1 / 4 := by
  rw [abs_lt] at hy
  rw [abs_le]
  rcases (abs_eq (by norm_num : (0 : ℤ) ≤ 1)).1 hcd with h | h
  · have hr : (d : ℝ) = c - 1 := by
      have : ((c - d : ℤ) : ℝ) = 1 := by exact_mod_cast h
      push_cast at this; linarith
    rw [hr] at hA hx
    constructor <;> nlinarith
  · have hr : (d : ℝ) = c + 1 := by
      have : ((c - d : ℤ) : ℝ) = -1 := by exact_mod_cast h
      push_cast at this; linarith
    rw [hr] at hA hx
    constructor <;> nlinarith

variable {S : Set (ℤ × ℤ)}

theorem corner_coord {a b : ℤ} (h : |a - b| = 1) :
    |((a : ℝ) + b) / 4 - a / 2| = 1 / 4 ∧ |((a : ℝ) + b) / 4 - b / 2| = 1 / 4 := by
  have h' : |((a : ℝ) - b)| = 1 := by
    have : ((|a - b| : ℤ) : ℝ) = 1 := by rw [h]; norm_num
    push_cast at this; exact this
  constructor
  · rw [show ((a : ℝ) + b) / 4 - a / 2 = -((a : ℝ) - b) / 4 by ring, abs_div, abs_neg, h']
    norm_num
  · rw [show ((a : ℝ) + b) / 4 - b / 2 = ((a : ℝ) - b) / 4 by ring, abs_div, h']
    norm_num

theorem sign_cases {a b : ℤ} (h : |a - b| = 1) : (b : ℝ) - a = 1 ∨ (b : ℝ) - a = -1 := by
  rw [abs_sub_comm] at h
  rcases (abs_eq (by norm_num : (0 : ℤ) ≤ 1)).1 h with h | h
  · left; exact_mod_cast h
  · right; exact_mod_cast h

theorem sq_eq_one_of_abs {a b : ℤ} (h : |a - b| = 1) : ((b : ℝ) - a) * (b - a) = 1 := by
  have h' : (b - a) * (b - a) = 1 := by
    rw [abs_sub_comm] at h
    rcases (abs_eq (by norm_num : (0 : ℤ) ≤ 1)).1 h with h | h <;> simp [h]
  have : (((b - a) * (b - a) : ℤ) : ℝ) = 1 := by rw [h']; norm_num
  push_cast at this; exact this

/-- At a checkerboard corner (`c, d` diagonal cells of `S`, the two other cells at the corner not
in `S`), the corner is a boundary point of the interior of the union which is not simple. -/
theorem exists_not_simple_of_checker (hS : S.Finite) {c d : ℤ × ℤ} (h1 : |c.1 - d.1| = 1)
    (h2 : |c.2 - d.2| = 1) (hc : c ∈ S) (hd : d ∈ S) (he : (d.1, c.2) ∉ S)
    (hf : (c.1, d.2) ∉ S) :
    ∃ x ∈ frontier (interior (cellUnion S)),
      ¬ IsSimpleBoundaryPoint (interior (cellUnion S)) x := by
  obtain ⟨x, hxdef⟩ : ∃ x : E2, x = pt ((c.1 + d.1) / 4) ((c.2 + d.2) / 4) := ⟨_, rfl⟩
  obtain ⟨w, hwdef⟩ : ∃ w : E2, w = pt (d.1 - c.1) (d.2 - c.2) := ⟨_, rfl⟩
  have hx0 : x 0 = (c.1 + d.1) / 4 := by rw [hxdef, pt_zero]
  have hx1 : x 1 = (c.2 + d.2) / 4 := by rw [hxdef, pt_one]
  have hw0 : w 0 = d.1 - c.1 := by rw [hwdef, pt_zero]
  have hw1 : w 1 = d.2 - c.2 := by rw [hwdef, pt_one]
  have hs1 := sq_eq_one_of_abs h1
  have hs2 := sq_eq_one_of_abs h2
  have hxe : x ∈ Cell (d.1, c.2) := by
    refine ⟨?_, ?_⟩
    · rw [hx0]; exact (corner_coord h1).2.le
    · rw [hx1]; exact (corner_coord h2).1.le
  have hxc : x ∈ Cell c := ⟨by rw [hx0]; exact (corner_coord h1).1.le,
    by rw [hx1]; exact (corner_coord h2).1.le⟩
  have hxΩ : x ∉ interior (cellUnion S) := notMem_interior he hxe
  have hxfr : x ∈ frontier (interior (cellUnion S)) := by
    rw [frontier_interior_cellUnion hS]
    exact exists_side hc he hxc hxe
  refine ⟨x, hxfr, ?_⟩
  have hc0 : Continuous fun q : E2 => q 0 := (EuclideanSpace.proj (0 : Fin 2) : E2 →L[ℝ] ℝ).continuous
  have hc1 : Continuous fun q : E2 => q 1 := (EuclideanSpace.proj (1 : Fin 2) : E2 →L[ℝ] ℝ).continuous
  have hf0 : Continuous fun q : E2 => (q 0 - x 0) * (d.1 - c.1) :=
    (hc0.sub continuous_const).mul continuous_const
  have hf1 : Continuous fun q : E2 => (q 1 - x 1) * (d.2 - c.2) :=
    (hc1.sub continuous_const).mul continuous_const
  obtain ⟨P, hPdef⟩ : ∃ P : Set E2, P =
      {q | 0 < (q 0 - x 0) * (d.1 - c.1)} ∩ {q | 0 < (q 1 - x 1) * (d.2 - c.2)} := ⟨_, rfl⟩
  obtain ⟨N, hNdef⟩ : ∃ N : Set E2, N =
      {q | (q 0 - x 0) * (d.1 - c.1) < 0} ∩ {q | (q 1 - x 1) * (d.2 - c.2) < 0} := ⟨_, rfl⟩
  have hPo : IsOpen P := hPdef ▸ (isOpen_lt continuous_const hf0).inter (isOpen_lt continuous_const hf1)
  have hNo : IsOpen N := hNdef ▸ (isOpen_lt hf0 continuous_const).inter (isOpen_lt hf1 continuous_const)
  have hPN : Disjoint P N := by
    rw [hPdef, hNdef]
    refine Set.disjoint_left.2 fun q hP hN => ?_
    have a : 0 < (q 0 - x 0) * (d.1 - c.1) := hP.1
    have b : (q 0 - x 0) * (d.1 - c.1) < 0 := hN.1
    linarith
  have hsplit : interior (cellUnion S) ∩ Metric.ball x (1 / 4) ⊆ P ∪ N := by
    rintro q ⟨hqΩ, hqb⟩
    have hd' : ∀ j, |q j - x j| < 1 / 4 := fun j => by
      rw [Metric.mem_ball] at hqb
      have := (PiLp.dist_apply_le q x j).trans_lt hqb
      rwa [Real.dist_eq] at this
    by_contra hq
    rw [hPdef, hNdef] at hq
    simp only [mem_union, mem_inter_iff, mem_setOf_eq, not_or, not_and_or, not_lt] at hq
    have key : ((q 0 - x 0) * (d.1 - c.1) ≤ 0 ∧ 0 ≤ (q 1 - x 1) * (d.2 - c.2)) ∨
        (0 ≤ (q 0 - x 0) * (d.1 - c.1) ∧ (q 1 - x 1) * (d.2 - c.2) ≤ 0) := by
      rcases le_total ((q 0 - x 0) * (d.1 - c.1)) 0 with a | a <;>
        rcases le_total ((q 1 - x 1) * (d.2 - c.2)) 0 with b | b <;> tauto
    rcases key with ⟨a, b⟩ | ⟨a, b⟩
    · have hb' : (q 1 - x 1) * (c.2 - d.2) ≤ 0 := by nlinarith
      exact notMem_interior hf ⟨coord_near_corner h1 hx0 (hd' 0) a,
        coord_near_corner (by rw [abs_sub_comm]; exact h2) (by rw [hx1]; ring) (hd' 1) hb'⟩ hqΩ
    · have ha' : (q 0 - x 0) * (c.1 - d.1) ≤ 0 := by nlinarith
      exact notMem_interior he ⟨coord_near_corner (by rw [abs_sub_comm]; exact h1)
        (by rw [hx0]; ring) (hd' 0) ha', coord_near_corner h2 hx1 (hd' 1) b⟩ hqΩ
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℕ → ℝ, ε = fun n : ℕ => 1 / 8 * (1 / ((n : ℝ) + 1)) := ⟨_, rfl⟩
  have hε0 : ∀ n, 0 < ε n := fun n => by rw [hεdef]; positivity
  have hε1 : ∀ n, ε n ≤ 1 / 8 := fun n => by
    rw [hεdef]
    have : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    simp only
    linarith
  have hplus : ∀ r : ℝ, 0 < r → r ≤ 1 / 8 → x + r • w ∈ OpenCell d ∧ x + r • w ∈ P := by
    intro r hr0 hr1
    have e0 : (x + r • w) 0 = (c.1 + d.1) / 4 + r * (d.1 - c.1) := by simp [hx0, hw0]
    have e1 : (x + r • w) 1 = (c.2 + d.2) / 4 + r * (d.2 - c.2) := by simp [hx1, hw1]
    rw [hPdef]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [e0, abs_lt]
      rcases sign_cases h1 with h | h <;> rw [h] <;> constructor <;> linarith
    · rw [e1, abs_lt]
      rcases sign_cases h2 with h | h <;> rw [h] <;> constructor <;> linarith
    · show 0 < ((x + r • w) 0 - x 0) * (d.1 - c.1)
      rw [e0, hx0]
      rcases sign_cases h1 with h | h <;> rw [h] <;> linarith
    · show 0 < ((x + r • w) 1 - x 1) * (d.2 - c.2)
      rw [e1, hx1]
      rcases sign_cases h2 with h | h <;> rw [h] <;> linarith
  have hminus : ∀ r : ℝ, 0 < r → r ≤ 1 / 8 → x - r • w ∈ OpenCell c ∧ x - r • w ∈ N := by
    intro r hr0 hr1
    have e0 : (x - r • w) 0 = (c.1 + d.1) / 4 - r * (d.1 - c.1) := by simp [hx0, hw0]
    have e1 : (x - r • w) 1 = (c.2 + d.2) / 4 - r * (d.2 - c.2) := by simp [hx1, hw1]
    rw [hNdef]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [e0, abs_lt]
      rcases sign_cases h1 with h | h <;> rw [h] <;> constructor <;> linarith
    · rw [e1, abs_lt]
      rcases sign_cases h2 with h | h <;> rw [h] <;> constructor <;> linarith
    · show ((x - r • w) 0 - x 0) * (d.1 - c.1) < 0
      rw [e0, hx0]
      rcases sign_cases h1 with h | h <;> rw [h] <;> linarith
    · show ((x - r • w) 1 - x 1) * (d.2 - c.2) < 0
      rw [e1, hx1]
      rcases sign_cases h2 with h | h <;> rw [h] <;> linarith
  obtain ⟨u, hudef⟩ : ∃ u : ℕ → E2,
      u = fun n => if Even n then x + ε n • w else x - ε n • w := ⟨_, rfl⟩
  have hu : ∀ n, u n ∈ interior (cellUnion S) := fun n => by
    rw [hudef]
    simp only
    split_ifs
    · exact openCell_subset_interior hd (hplus _ (hε0 n) (hε1 n)).1
    · exact openCell_subset_interior hc (hminus _ (hε0 n) (hε1 n)).1
  have hlim : Tendsto u atTop (𝓝 x) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hε : Tendsto ε atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 / 8 : ℝ)
      rw [mul_zero] at this
      rw [hεdef]
      exact this
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      (by simpa using hε.mul_const ‖w‖)
    rw [hudef]
    simp only
    split_ifs
    · simp [norm_smul, abs_of_pos (hε0 n)]
    · simp [norm_smul, abs_of_pos (hε0 n)]
  refine not_simple_of_split hxΩ (by norm_num : (0 : ℝ) < 1 / 4) hPo hNo hPN hsplit hu hlim
    (fun k => ?_) (fun k => ?_)
  · have : u (2 * k) = x + ε (2 * k) • w := by simp [hudef]
    rw [this]; exact (hplus _ (hε0 _) (hε1 _)).2
  · have : u (2 * k + 1) = x - ε (2 * k + 1) • w := by simp [hudef]
    rw [this]; exact (hminus _ (hε0 _) (hε1 _)).2

/-- If every boundary point of the interior of a finite union of cells is simple, there is no
checkerboard corner. -/
theorem noChecker_of_simple (hS : S.Finite)
    (hsimple : ∀ x ∈ frontier (interior (cellUnion S)),
      IsSimpleBoundaryPoint (interior (cellUnion S)) x) : NoChecker S := by
  intro c d h1 h2 hcd hef
  by_contra hce
  by_cases hc : c ∈ S
  · obtain ⟨x, hx, hns⟩ := exists_not_simple_of_checker hS h1 h2 hc (hcd.1 hc)
      (fun he => hce ⟨fun _ => he, fun _ => hc⟩) (fun hf => hce ⟨fun _ => hef.2 hf, fun _ => hc⟩)
    exact hns (hsimple x hx)
  · have he : (d.1, c.2) ∈ S := by tauto
    have hf : (c.1, d.2) ∈ S := hef.1 he
    obtain ⟨x, hx, hns⟩ := exists_not_simple_of_checker hS (c := (d.1, c.2)) (d := (c.1, d.2))
      (by simpa [abs_sub_comm] using h1) h2 he hf (fun h => hc h)
      (fun h => hc (hcd.2 h))
    exact hns (hsimple x hx)

end Rigidity.Proofs.Topology.Polyomino
