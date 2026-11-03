import Rigidity.Proofs.Section5.AnnulusCrossings
import LatticeProb.Lattice.Planar.Winding

/-!
# Lemma 5.14: the loop around an annulus from the crossings

This file proves `LoopFromCrossingsStep` (`step:5.14-planarity`),
the deterministic planarity step of Lemma 5.14 (corrected draft L1945-1959). No literature input
is used: the only planar topology is the following discrete crossing lemma.

* `exists_reachIn_of_crossing`: an open path in the horizontal strip `ℝ × [y_a, y_b]` from
  `x ≤ x_a` to `x ≥ x_b` and an open path in the vertical strip `[x_a, x_b] × ℝ` from `y ≤ y_a` to
  `y ≥ y_b` share a vertex. Its proof uses the crossing number `LatticeProb.Lattice.Planar.wind`
  of the horizontal path with the eastward ray from a point: along the vertical path, this
  crossing number plus the indicator of lying above the endpoint of the horizontal path is
  constant, while it equals `0` at the bottom and `1` at the top.

The loop at scale `R` is built from the four crossings of the annulus `Q_{2R} \ Q_R`: the bottom
crossing meets the left and the right crossings, the top crossing meets them too, and the four
arcs between the four meeting points form a closed walk. Along the bottom, right and top arcs the
principal argument is continuous (the arcs lie in the open lower, right and upper half-planes),
and along the left arc the argument of `-z` is; summing the increments gives `2π`, so the winding
number is `1`. The radial crossings join the right crossing at scale `R` to the right crossing at
scale `2R`, so the loop is joined by open paths to vertices with arbitrarily large first
coordinate: its open cluster is infinite, hence it is the unique infinite cluster.

With `crossingProbabilityStep` and `borelCantelliStep` (`AnnulusCrossings.lean`), this gives
Lemma 5.14 (`loopsAroundAnnuli`) from Kesten's crossing estimate `KestenRectangleCrossing` and the
almost sure uniqueness of the infinite cluster.
-/

open MeasureTheory LatticeProb.Percolation LatticeProb.Lattice

namespace Rigidity.Proofs.Section5

open Rigidity.Section5 Rigidity.External Rigidity.Steps.Section5

/-! ### Crossing numbers of open lattice walks -/

/-- A vertex of `ℤ²` as a site of the planar lattice `ℤ × ℤ`. -/
def toSite (v : Vertex 2) : ℤ × ℤ := (v 0, v 1)

theorem toSite_injective : Function.Injective toSite := by
  intro v w h
  simp only [toSite, Prod.mk.injEq] at h
  funext i
  fin_cases i
  · exact h.1
  · exact h.2

/-- The steps of a list with unit steps are unit vectors. -/
theorem steps_unit_of_isChain {c : List (ℤ × ℤ)}
    (hc : c.IsChain (fun a b => Planar.IsUnit (b - a))) {s : (ℤ × ℤ) × (ℤ × ℤ)}
    (hs : s ∈ Planar.steps c) : Planar.IsUnit (s.2 - s.1) := by
  unfold Planar.steps at hs
  obtain ⟨i, hi, hs'⟩ := List.mem_iff_getElem.1 hs
  rw [List.getElem_zip] at hs'
  subst hs'
  simp only [List.length_zip, List.length_tail, lt_min_iff] at hi
  have := List.isChain_iff_getElem.1 hc i (by omega)
  simpa [List.getElem_tail] using this

/-- Below a walk the crossing number vanishes. -/
theorem wind_eq_zero_of_lt {c : List (ℤ × ℤ)} {y : ℤ × ℤ} (hy : ∀ p ∈ c, y.2 < p.2) :
    Planar.wind c y = 0 := by
  unfold Planar.wind
  refine List.sum_eq_zero (fun z hz => ?_)
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hz
  have h1 := hy _ (Planar.mem_steps hs).1
  have h2 := hy _ (Planar.mem_steps hs).2
  unfold Planar.stepWind
  split_ifs <;> omega

/-- At or above the top of a walk the crossing number vanishes. -/
theorem wind_eq_zero_of_le {c : List (ℤ × ℤ)} {y : ℤ × ℤ} (hy : ∀ p ∈ c, p.2 ≤ y.2) :
    Planar.wind c y = 0 := by
  unfold Planar.wind
  refine List.sum_eq_zero (fun z hz => ?_)
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hz
  have h1 := hy _ (Planar.mem_steps hs).1
  have h2 := hy _ (Planar.mem_steps hs).2
  unfold Planar.stepWind
  split_ifs <;> omega

/-- A horizontal move off a walk with unit steps does not change its crossing number. -/
theorem wind_eq_wind_add_right {c : List (ℤ × ℤ)}
    (hc : c.IsChain (fun a b => Planar.IsUnit (b - a))) {y : ℤ × ℤ} (hy : y + (1, 0) ∉ c) :
    Planar.wind c y = Planar.wind c (y + (1, 0)) := by
  unfold Planar.wind
  rw [← sub_eq_zero, Planar.sum_map_sub']
  refine List.sum_eq_zero (fun z hz => ?_)
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hz
  have hm := Planar.mem_steps hs
  have hu := steps_unit_of_isChain hc hs
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := s
  obtain ⟨y1, y2⟩ := y
  have h1 : (a1, a2) ≠ (y1 + 1, y2) := fun h => hy (by
    rw [Prod.mk_add_mk, add_zero, ← h]; exact hm.1)
  have h2 : (b1, b2) ≠ (y1 + 1, y2) := fun h => hy (by
    rw [Prod.mk_add_mk, add_zero, ← h]; exact hm.2)
  rw [Planar.isUnit_iff'] at hu
  simp only [Prod.mk_add_mk, Prod.mk.injEq, ne_eq, not_and] at h1 h2 ⊢
  unfold Planar.stepWind
  dsimp only
  rcases hu with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> split_ifs <;> omega

/-- A vertical move off a walk with unit steps changes its crossing number by the endpoint terms. -/
theorem wind_sub_wind_add_up {a : ℤ × ℤ} {l : List (ℤ × ℤ)}
    (hc : (a :: l).IsChain (fun a b => Planar.IsUnit (b - a))) {y : ℤ × ℤ}
    (hy : y + (0, 1) ∉ a :: l) :
    Planar.wind (a :: l) y - Planar.wind (a :: l) (y + (0, 1)) =
      (if y.1 + 1 ≤ ((a :: l).getLast (List.cons_ne_nil a l)).1 ∧
          ((a :: l).getLast (List.cons_ne_nil a l)).2 = y.2 + 1 then (1 : ℤ) else 0) -
        (if y.1 + 1 ≤ a.1 ∧ a.2 = y.2 + 1 then (1 : ℤ) else 0) := by
  unfold Planar.wind
  rw [Planar.sum_map_sub']
  have key : ∀ s ∈ Planar.steps (a :: l),
      Planar.stepWind y s - Planar.stepWind (y + (0, 1)) s =
        (fun p : ℤ × ℤ => if y.1 + 1 ≤ p.1 ∧ p.2 = y.2 + 1 then (1 : ℤ) else 0) s.2 -
          (fun p : ℤ × ℤ => if y.1 + 1 ≤ p.1 ∧ p.2 = y.2 + 1 then (1 : ℤ) else 0) s.1 := by
    intro s hs
    have hm := Planar.mem_steps hs
    exact Planar.stepWind_row y (steps_unit_of_isChain hc hs)
      (fun h => hy (h ▸ hm.1)) (fun h => hy (h ▸ hm.2))
  rw [List.map_congr_left key]
  exact Planar.sum_steps_sub
    (fun p : ℤ × ℤ => if y.1 + 1 ≤ p.1 ∧ p.2 = y.2 + 1 then (1 : ℤ) else 0) a l

/-- The crossing number of `c` plus the indicator of lying at height at least `h`. -/
def crossPot (c : List (ℤ × ℤ)) (h : ℤ) (y : ℤ × ℤ) : ℤ :=
  Planar.wind c y + if h ≤ y.2 then 1 else 0

/-- One unit step inside the vertical strip `[xa, xb] × ℤ`, off a walk `c` from `x ≤ xa` to
`x ≥ xb`, does not change `crossPot c` at the height of the endpoint of `c`. -/
theorem crossPot_eq_of_isUnit {a e : ℤ × ℤ} {l : List (ℤ × ℤ)}
    (hc : (a :: l).IsChain (fun a b => Planar.IsUnit (b - a)))
    (he : (a :: l).getLast (List.cons_ne_nil a l) = e) {xa xb : ℤ} (ha : a.1 ≤ xa)
    (hb : xb ≤ e.1) {u v : ℤ × ℤ} (huv : Planar.IsUnit (v - u)) (hu : u ∉ a :: l)
    (hv : v ∉ a :: l) (hu1 : xa ≤ u.1 ∧ u.1 ≤ xb) :
    crossPot (a :: l) e.2 u = crossPot (a :: l) e.2 v := by
  have heM : e ∈ a :: l := he ▸ List.getLast_mem _
  have hv' : v = u + (v - u) := by abel
  unfold crossPot
  rcases huv with h | h | h | h <;> rw [h] at hv' <;> subst hv'
  · rw [wind_eq_wind_add_right hc hv]
    simp
  · have e1 : u + (-1, 0) + (1, 0) = u := by ext <;> simp
    have := wind_eq_wind_add_right hc (y := u + (-1, 0)) (by rwa [e1])
    rw [e1] at this
    rw [this]
    simp
  · have key := wind_sub_wind_add_up hc hv
    rw [he] at key
    obtain ⟨u1, u2⟩ := u
    obtain ⟨e1, e2⟩ := e
    obtain ⟨a1, a2⟩ := a
    have hne : (u1, u2 + 1) ≠ (e1, e2) := fun h => hv (by
      rw [Prod.mk_add_mk, add_zero, h]; exact heM)
    simp only [Prod.mk_add_mk, add_zero, ne_eq, Prod.mk.injEq, not_and] at hne key hu1 ha hb ⊢
    split_ifs at key ⊢ <;> omega
  · have e1 : u + (0, -1) + (0, 1) = u := by ext <;> simp
    have key := wind_sub_wind_add_up hc (y := u + (0, -1)) (by rwa [e1])
    rw [e1, he] at key
    obtain ⟨u1, u2⟩ := u
    obtain ⟨e1, e2⟩ := e
    obtain ⟨a1, a2⟩ := a
    have hne : (u1, u2) ≠ (e1, e2) := fun h => hu (by rw [h]; exact heM)
    simp only [Prod.mk_add_mk, add_zero, ne_eq, Prod.mk.injEq, not_and] at hne key hu1 ha hb ⊢
    split_ifs at key ⊢ <;> omega

/-! ### Open paths inside a set and the crossing lemma -/

variable {ω : Configuration 2}

/-- An open edge of `ℤ²` is a unit step of `ℤ × ℤ`. -/
theorem isUnit_toSite_of_adj {u v : Vertex 2} (h : (openGraph ω).Adj u v) :
    Planar.IsUnit (toSite v - toSite u) := by
  obtain ⟨hadj, -⟩ := h
  have h1 := lattice_adj_iff_l1Dist.1 hadj
  simp only [latticeL1Dist, Fin.sum_univ_two] at h1
  simp only [Planar.IsUnit, toSite, Prod.mk_sub_mk, Prod.mk.injEq]
  rcases abs_cases (u 0 - v 0) with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
    rcases abs_cases (u 1 - v 1) with ⟨h3, _⟩ | ⟨h3, _⟩ <;> omega

/-- `x` and `y` are joined by an open path inside `S`. -/
def ReachIn (ω : Configuration 2) (S : Set (Vertex 2)) (x y : Vertex 2) : Prop :=
  ∃ W : (openGraph ω).Walk x y, ∀ w ∈ W.support, w ∈ S

theorem ReachIn.symm {S : Set (Vertex 2)} {x y : Vertex 2} (h : ReachIn ω S x y) :
    ReachIn ω S y x := by
  obtain ⟨W, hW⟩ := h
  exact ⟨W.reverse, fun w hw => hW w (by
    rwa [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hw)⟩

theorem ReachIn.trans {S : Set (Vertex 2)} {x y z : Vertex 2} (h1 : ReachIn ω S x y)
    (h2 : ReachIn ω S y z) : ReachIn ω S x z := by
  obtain ⟨W1, h1⟩ := h1
  obtain ⟨W2, h2⟩ := h2
  refine ⟨W1.append W2, fun w hw => ?_⟩
  rcases (SimpleGraph.Walk.mem_support_append_iff W1 W2).1 hw with hw | hw
  exacts [h1 w hw, h2 w hw]

theorem ReachIn.reachable {S : Set (Vertex 2)} {x y : Vertex 2} (h : ReachIn ω S x y) :
    (openGraph ω).Reachable x y :=
  ⟨h.choose⟩

/-- A vertex of an open path inside `S` is joined inside `S` to the start of the path. -/
theorem reachIn_of_mem_support {S : Set (Vertex 2)} {x y w : Vertex 2}
    (W : (openGraph ω).Walk x y) (hW : ∀ v ∈ W.support, v ∈ S) (hw : w ∈ W.support) :
    ReachIn ω S x w :=
  ⟨W.takeUntil w hw, fun v hv => hW v (W.support_takeUntil_subset_support hw hv)⟩

/-- Reachability in the open graph induced on `S` is `ReachIn`. -/
theorem reachIn_of_reachable_induce {S : Set (Vertex 2)} {x y : Vertex 2} {hx : x ∈ S}
    {hy : y ∈ S} (h : ((openGraph ω).induce S).Reachable ⟨x, hx⟩ ⟨y, hy⟩) :
    ReachIn ω S x y := by
  obtain ⟨W⟩ := h
  have key : ∀ w ∈ (W.map (SimpleGraph.Embedding.induce S).toHom).support, w ∈ S := by
    intro w hw
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hw
    obtain ⟨w', -, rfl⟩ := hw
    exact w'.2
  exact ⟨_, key⟩

/-- **The crossing lemma.** An open path in the horizontal strip `ℤ × [ya, yb]` from `x ≤ xa` to
`x ≥ xb` and an open path in the vertical strip `[xa, xb] × ℤ` from `y ≤ ya` to `y ≥ yb` share a
vertex. -/
theorem exists_mem_support_of_crossing {y z y' z' : Vertex 2} (P : (openGraph ω).Walk y z)
    (Q : (openGraph ω).Walk y' z') {xa xb ya yb : ℤ}
    (hP : ∀ w ∈ P.support, ya ≤ w 1 ∧ w 1 ≤ yb) (hQ : ∀ w ∈ Q.support, xa ≤ w 0 ∧ w 0 ≤ xb)
    (hy : y 0 ≤ xa) (hz : xb ≤ z 0) (hy' : y' 1 ≤ ya) (hz' : yb ≤ z' 1) :
    ∃ w ∈ P.support, w ∈ Q.support := by
  by_contra hne
  push Not at hne
  obtain ⟨t, ht⟩ : ∃ t, P.support = y :: t := ⟨_, P.cons_tail_support.symm⟩
  have hmem : ∀ v, v ∈ toSite y :: t.map toSite ↔ ∃ w ∈ P.support, toSite w = v := by
    intro v
    rw [ht, ← List.map_cons, List.mem_map]
  have hchain : (toSite y :: t.map toSite).IsChain (fun a b => Planar.IsUnit (b - a)) := by
    have h1 := P.isChain_adj_support
    rw [ht] at h1
    have h2 := (List.isChain_map toSite (R := fun a b => Planar.IsUnit (b - a))).2
      (h1.imp fun _ _ h => isUnit_toSite_of_adj h)
    simpa using h2
  have hlast : (toSite y :: t.map toSite).getLast (List.cons_ne_nil _ _) = toSite z := by
    have h1 : (y :: t).getLast (List.cons_ne_nil _ _) = z := by
      simpa [ht] using P.getLast_support
    rw [← h1, ← List.getLast_map (f := toSite)]
    rfl
  have hcQ : ∀ w ∈ Q.support, toSite w ∉ toSite y :: t.map toSite := by
    intro w hw hw'
    obtain ⟨w', hw', heq⟩ := (hmem _).1 hw'
    exact hne w' hw' (toSite_injective heq ▸ hw)
  have hconst : ∀ {u v : Vertex 2} (W : (openGraph ω).Walk u v),
      (∀ w ∈ W.support, w ∈ Q.support) →
      crossPot (toSite y :: t.map toSite) (toSite z).2 (toSite u) =
        crossPot (toSite y :: t.map toSite) (toSite z).2 (toSite v) := by
    intro u v W
    induction W with
    | nil => intro _; rfl
    | cons h p ih =>
      intro hW
      have hu := hW _ (List.mem_cons_self ..)
      have hv := hW _ (List.mem_cons_of_mem _ p.start_mem_support)
      rw [crossPot_eq_of_isUnit hchain hlast hy hz (isUnit_toSite_of_adj h) (hcQ _ hu)
        (hcQ _ hv) (hQ _ hu)]
      exact ih (fun w hw => hW w (List.mem_cons_of_mem _ hw))
  have hQ0 := hQ _ Q.start_mem_support
  have hbot : (y' 0, y' 1 - 1) ∉ toSite y :: t.map toSite := by
    intro h
    obtain ⟨w, hw, heq⟩ := (hmem _).1 h
    simp only [toSite, Prod.mk.injEq] at heq
    have := (hP w hw).1
    omega
  have h0 := crossPot_eq_of_isUnit hchain hlast hy hz (u := (y' 0, y' 1 - 1)) (v := toSite y')
    (by right; right; left; simp [toSite]) hbot (hcQ _ Q.start_mem_support) hQ0
  rw [hconst Q (fun w hw => hw)] at h0
  have hlow : Planar.wind (toSite y :: t.map toSite) (y' 0, y' 1 - 1) = 0 := by
    refine wind_eq_zero_of_lt fun p hp => ?_
    obtain ⟨w, hw, rfl⟩ := (hmem _).1 hp
    have := (hP w hw).1
    simp only [toSite]
    omega
  have hhigh : Planar.wind (toSite y :: t.map toSite) (toSite z') = 0 := by
    refine wind_eq_zero_of_le fun p hp => ?_
    obtain ⟨w, hw, rfl⟩ := (hmem _).1 hp
    have := (hP w hw).2
    simp only [toSite]
    omega
  have hz1 := hP z P.end_mem_support
  unfold crossPot at h0
  rw [hlow, hhigh] at h0
  simp only [toSite] at h0
  split_ifs at h0 <;> omega

/-- The crossing lemma for open paths inside two sets contained in a horizontal and a vertical
strip: the meeting vertex is joined to the starts of both paths inside the respective sets. -/
theorem exists_reachIn_of_crossing {S T : Set (Vertex 2)} {y z y' z' : Vertex 2}
    (hP : ReachIn ω S y z) (hQ : ReachIn ω T y' z') {xa xb ya yb : ℤ}
    (hS : ∀ w ∈ S, ya ≤ w 1 ∧ w 1 ≤ yb) (hT : ∀ w ∈ T, xa ≤ w 0 ∧ w 0 ≤ xb)
    (hy : y 0 ≤ xa) (hz : xb ≤ z 0) (hy' : y' 1 ≤ ya) (hz' : yb ≤ z' 1) :
    ∃ w, ReachIn ω S y w ∧ ReachIn ω T y' w := by
  obtain ⟨P, hPS⟩ := hP
  obtain ⟨Q, hQT⟩ := hQ
  obtain ⟨w, hwP, hwQ⟩ := exists_mem_support_of_crossing P Q (fun w hw => hS w (hPS w hw))
    (fun w hw => hT w (hQT w hw)) hy hz hy' hz'
  exact ⟨w, reachIn_of_mem_support P hPS hwP, reachIn_of_mem_support Q hQT hwQ⟩

/-! ### The winding number of a loop made of four arcs -/

/-- If the arguments of `z` and `w` differ by less than `π`, the argument of `w / z` is their
difference. -/
theorem arg_div_eq_sub {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0)
    (h1 : -Real.pi < Complex.arg w - Complex.arg z) (h2 : Complex.arg w - Complex.arg z < Real.pi) :
    Complex.arg (w / z) = Complex.arg w - Complex.arg z := by
  rw [← Complex.arg_coe_angle_toReal_eq_arg (w / z), Complex.arg_div_coe_angle hw hz,
    ← Real.Angle.coe_sub, Real.Angle.toReal_coe_eq_self_iff]
  exact ⟨h1, h2.le⟩

theorem toComplex_re (v : Vertex 2) : (toComplex v).re = v 0 := rfl

theorem toComplex_im (v : Vertex 2) : (toComplex v).im = v 1 := rfl

theorem toComplex_ne_zero_of_im {v : Vertex 2} (h : v 1 ≠ 0) : toComplex v ≠ 0 := fun h0 =>
  h (by exact_mod_cast (toComplex_im v).symm.trans (congrArg Complex.im h0))

theorem toComplex_ne_zero_of_re {v : Vertex 2} (h : v 0 ≠ 0) : toComplex v ≠ 0 := fun h0 =>
  h (by exact_mod_cast (toComplex_re v).symm.trans (congrArg Complex.re h0))

/-- In the open lower half-plane the principal argument is continuous. -/
theorem arg_div_of_im_neg {v w : Vertex 2} (hv : v 1 < 0) (hw : w 1 < 0) :
    Complex.arg (toComplex w / toComplex v) = Complex.arg (toComplex w) - Complex.arg (toComplex v) := by
  have av := Complex.arg_neg_iff.2 (show (toComplex v).im < 0 by
    rw [toComplex_im]; exact_mod_cast hv)
  have aw := Complex.arg_neg_iff.2 (show (toComplex w).im < 0 by
    rw [toComplex_im]; exact_mod_cast hw)
  have := Complex.neg_pi_lt_arg (toComplex v)
  have := Complex.neg_pi_lt_arg (toComplex w)
  exact arg_div_eq_sub (toComplex_ne_zero_of_im hv.ne) (toComplex_ne_zero_of_im hw.ne)
    (by linarith) (by linarith)

/-- In the open upper half-plane the principal argument is continuous. -/
theorem arg_div_of_im_pos {v w : Vertex 2} (hv : 0 < v 1) (hw : 0 < w 1) :
    Complex.arg (toComplex w / toComplex v) = Complex.arg (toComplex w) - Complex.arg (toComplex v) := by
  have hv' : 0 < (toComplex v).im := by rw [toComplex_im]; exact_mod_cast hv
  have hw' : 0 < (toComplex w).im := by rw [toComplex_im]; exact_mod_cast hw
  have av := Complex.arg_nonneg_iff.2 hv'.le
  have aw := Complex.arg_nonneg_iff.2 hw'.le
  have av' := Complex.arg_lt_pi_iff.2 (Or.inr hv'.ne')
  have aw' := Complex.arg_lt_pi_iff.2 (Or.inr hw'.ne')
  exact arg_div_eq_sub (toComplex_ne_zero_of_im hv.ne') (toComplex_ne_zero_of_im hw.ne')
    (by linarith) (by linarith)

/-- In the open right half-plane the principal argument is continuous. -/
theorem arg_div_of_re_pos {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re) :
    Complex.arg (w / z) = Complex.arg w - Complex.arg z := by
  have az := abs_lt.1 (Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hz))
  have aw := abs_lt.1 (Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hw))
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  exact arg_div_eq_sub hz0 hw0 (by linarith) (by linarith)

/-- In the open left half-plane the argument of `-z` is continuous. -/
theorem arg_div_of_re_neg {v w : Vertex 2} (hv : v 0 < 0) (hw : w 0 < 0) :
    Complex.arg (toComplex w / toComplex v) =
      Complex.arg (-toComplex w) - Complex.arg (-toComplex v) := by
  rw [← neg_div_neg_eq]
  refine arg_div_of_re_pos ?_ ?_ <;> rw [Complex.neg_re, toComplex_re] <;>
    [exact neg_pos.2 (by exact_mod_cast hv); exact neg_pos.2 (by exact_mod_cast hw)]

/-- Along a walk in a set on which `θ` is a continuous branch of the argument, the argument
increments add up to the increment of `θ`. -/
theorem sum_darts_arg {G : SimpleGraph (Vertex 2)} {u v : Vertex 2} (W : G.Walk u v)
    (θ : Vertex 2 → ℝ) (S : Set (Vertex 2)) (hW : ∀ w ∈ W.support, w ∈ S)
    (hθ : ∀ a ∈ S, ∀ b ∈ S, Complex.arg (toComplex b / toComplex a) = θ b - θ a) :
    (W.darts.map (fun d => Complex.arg (toComplex d.snd / toComplex d.fst))).sum = θ v - θ u := by
  induction W with
  | nil => simp
  | cons h p ih =>
    rw [SimpleGraph.Walk.darts_cons, List.map_cons, List.sum_cons,
      ih (fun w hw => hW w (List.mem_cons_of_mem _ hw))]
    have := hθ _ (hW _ (List.mem_cons_self ..)) _
      (hW _ (List.mem_cons_of_mem _ p.start_mem_support))
    dsimp only
    rw [this]
    ring

/-- Sums over the steps of a walk, indexed by position, are sums over its darts. -/
theorem sum_range_getVert {V : Type*} {G : SimpleGraph V} {u v : V} (W : G.Walk u v)
    (F : V → V → ℝ) :
    ∑ i ∈ Finset.range W.length, F (W.getVert i) (W.getVert (i + 1)) =
      (W.darts.map (fun d => F d.fst d.snd)).sum := by
  induction W with
  | nil => simp
  | cons h p ih =>
    rw [SimpleGraph.Walk.length_cons, Finset.sum_range_succ', SimpleGraph.Walk.darts_cons,
      List.map_cons, List.sum_cons]
    simp only [SimpleGraph.Walk.getVert_cons_succ, SimpleGraph.Walk.getVert_zero]
    rw [ih]
    exact add_comm _ _

/-- On a closed walk of length `n + 1`, the vertex after position `i : Fin (n + 1)` (cyclically)
is the vertex at position `i + 1`. -/
theorem getVert_fin_succ {V : Type*} {G : SimpleGraph V} {u : V} (W : G.Walk u u) {n : ℕ}
    (hn : W.length = n + 1) (i : Fin (n + 1)) :
    W.getVert ((i + 1 : Fin (n + 1)) : ℕ) = W.getVert ((i : ℕ) + 1) := by
  rw [Fin.val_add_one]
  split_ifs with h
  · rw [h, Fin.val_last, ← hn, SimpleGraph.Walk.getVert_length, SimpleGraph.Walk.getVert_zero]
  · rfl

/-- Cyclic sums over the vertices of a closed walk are sums over its darts. -/
theorem sum_fin_getVert {V : Type*} {G : SimpleGraph V} {u : V} (W : G.Walk u u) {n : ℕ}
    (hn : W.length = n + 1) (F : V → V → ℝ) :
    ∑ i : Fin (n + 1), F (W.getVert i) (W.getVert ((i + 1 : Fin (n + 1)) : ℕ)) =
      (W.darts.map (fun d => F d.fst d.snd)).sum := by
  rw [← sum_range_getVert, hn, ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun i _ => by rw [getVert_fin_succ W hn i]

/-- A closed walk made of an arc in the lower half-plane, an arc in the right half-plane, an arc
in the upper half-plane and an arc in the left half-plane has total argument increment `2π`. -/
theorem sum_darts_arg_four_arcs {G : SimpleGraph (Vertex 2)} {p1 p2 p3 p4 : Vertex 2}
    (W1 : G.Walk p1 p2) (W2 : G.Walk p2 p3) (W3 : G.Walk p3 p4) (W4 : G.Walk p4 p1)
    (h1 : ∀ w ∈ W1.support, w 1 < 0) (h2 : ∀ w ∈ W2.support, 0 < w 0)
    (h3 : ∀ w ∈ W3.support, 0 < w 1) (h4 : ∀ w ∈ W4.support, w 0 < 0) :
    ((W1.append (W2.append (W3.append W4))).darts.map
      (fun d => Complex.arg (toComplex d.snd / toComplex d.fst))).sum = 2 * Real.pi := by
  simp only [SimpleGraph.Walk.darts_append, List.map_append, List.sum_append]
  rw [sum_darts_arg W1 (fun v => Complex.arg (toComplex v)) {w | w 1 < 0} h1
      (fun a ha b hb => arg_div_of_im_neg ha hb),
    sum_darts_arg W2 (fun v => Complex.arg (toComplex v)) {w | 0 < w 0} h2
      (fun a ha b hb => arg_div_of_re_pos (by rw [toComplex_re]; exact_mod_cast ha)
        (by rw [toComplex_re]; exact_mod_cast hb)),
    sum_darts_arg W3 (fun v => Complex.arg (toComplex v)) {w | 0 < w 1} h3
      (fun a ha b hb => arg_div_of_im_pos ha hb),
    sum_darts_arg W4 (fun v => Complex.arg (-toComplex v)) {w | w 0 < 0} h4
      (fun a ha b hb => arg_div_of_re_neg ha hb)]
  have hp1 : (toComplex p1).im < 0 := by
    rw [toComplex_im]; exact_mod_cast h1 _ W1.start_mem_support
  have hp4 : 0 < (toComplex p4).im := by
    rw [toComplex_im]; exact_mod_cast h3 _ W3.end_mem_support
  simp only [Complex.arg_neg_eq_arg_add_pi_of_im_neg hp1,
    Complex.arg_neg_eq_arg_sub_pi_of_im_pos hp4]
  ring

/-! ### The crossings at all scales lie in the unique infinite cluster -/

theorem ReachIn.mono {S T : Set (Vertex 2)} {x y : Vertex 2} (h : ReachIn ω S x y)
    (hST : S ⊆ T) : ReachIn ω T x y := by
  obtain ⟨W, hW⟩ := h
  exact ⟨W, fun w hw => hST (hW w hw)⟩

theorem ReachIn.start_mem {S : Set (Vertex 2)} {x y : Vertex 2} (h : ReachIn ω S x y) : x ∈ S := by
  obtain ⟨W, hW⟩ := h
  exact hW x W.start_mem_support

theorem ReachIn.end_mem {S : Set (Vertex 2)} {x y : Vertex 2} (h : ReachIn ω S x y) : y ∈ S := by
  obtain ⟨W, hW⟩ := h
  exact hW y W.end_mem_support

/-- A crossing in direction `0` of the rectangle `[a, a + m] × [b, b + n]`. -/
theorem exists_reachIn_of_hasOpenCrossing_zero {a b : ℤ} {m n : ℕ}
    (h : HasOpenCrossing ω ![a, b] m n 0) :
    ∃ y z, ReachIn ω {w | (a ≤ w 0 ∧ w 0 ≤ a + m) ∧ b ≤ w 1 ∧ w 1 ≤ b + n} y z ∧
      y 0 = a ∧ z 0 = a + m := by
  obtain ⟨y, z, hy, hz, hyi, hzi, hr⟩ := h
  refine ⟨y, z, (reachIn_of_reachable_induce hr).mono fun w hw => ?_, by simpa using hyi,
    by simpa using hzi⟩
  simpa [crossingRectangle, Fin.forall_fin_two] using hw

/-- A crossing in direction `1` of the rectangle `[a, a + n] × [b, b + m]`. -/
theorem exists_reachIn_of_hasOpenCrossing_one {a b : ℤ} {m n : ℕ}
    (h : HasOpenCrossing ω ![a, b] m n 1) :
    ∃ y z, ReachIn ω {w | (a ≤ w 0 ∧ w 0 ≤ a + n) ∧ b ≤ w 1 ∧ w 1 ≤ b + m} y z ∧
      y 1 = b ∧ z 1 = b + m := by
  obtain ⟨y, z, hy, hz, hyi, hzi, hr⟩ := h
  refine ⟨y, z, (reachIn_of_reachable_induce hr).mono fun w hw => ?_, by simpa using hyi,
    by simpa using hzi⟩
  simpa [crossingRectangle, Fin.forall_fin_two] using hw

/-- `v` is joined by open paths to vertices with arbitrarily large first coordinate. -/
def Escapes (ω : Configuration 2) (v : Vertex 2) : Prop :=
  ∀ N : ℤ, ∃ w, (openGraph ω).Reachable v w ∧ N ≤ w 0

theorem Escapes.of_reachable {v w : Vertex 2} (h : (openGraph ω).Reachable v w)
    (hv : Escapes ω v) : Escapes ω w := fun N => by
  obtain ⟨u, hu, hu0⟩ := hv N
  exact ⟨u, h.symm.trans hu, hu0⟩

/-- A vertex joined to vertices with arbitrarily large first coordinate lies in the unique
infinite cluster. -/
theorem mem_uniqueInfiniteComponent_of_escapes (h : HasUniqueInfiniteOpenComponent ω)
    {v : Vertex 2} (hv : Escapes ω v) : v ∈ uniqueInfiniteComponent h := by
  refine (mem_uniqueInfiniteComponent_iff h v).2 ?_
  show ((openGraph ω).connectedComponentMk v).supp.Infinite
  by_contra hfin
  rw [Set.not_infinite] at hfin
  obtain ⟨N, hN⟩ := (hfin.image (fun w : Vertex 2 => w 0)).bddAbove
  obtain ⟨w, hvw, hw⟩ := hv (N + 1)
  have hw' : w ∈ ((openGraph ω).connectedComponentMk v).supp :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).2
      (SimpleGraph.ConnectedComponent.sound hvw.symm)
  have : w 0 ≤ N := hN ⟨w, hw', rfl⟩
  omega

/-- The radial crossings join a vertical crossing of `[R + 1, 2R] × [0, R]` to vertices with first
coordinate at least `2^k R`. -/
theorem exists_reachable_of_annulusCrossings {M : ℕ}
    (hM : ∀ R : ℕ, M ≤ R → AnnulusCrossings ω R) (k : ℕ) :
    ∀ R : ℕ, M ≤ R → 1 ≤ R → ∀ y z : Vertex 2,
      ReachIn ω {w | (R : ℤ) + 1 ≤ w 0 ∧ w 0 ≤ 2 * R} y z → y 1 ≤ 0 → (R : ℤ) ≤ z 1 →
      ∃ w, (openGraph ω).Reachable y w ∧ 2 ^ k * (R : ℤ) ≤ w 0 := by
  induction k with
  | zero =>
    intro R _ _ y z hyz _ _
    have := hyz.start_mem.1
    exact ⟨y, SimpleGraph.Reachable.refl y, by rw [pow_zero, one_mul]; omega⟩
  | succ k ih =>
    intro R hMR hR y z hyz hy hz
    obtain ⟨-, -, -, -, hq⟩ := hM R hMR
    obtain ⟨yq, zq, hQ, hyq, hzq⟩ := exists_reachIn_of_hasOpenCrossing_zero hq
    obtain ⟨-, -, -, hr2, -⟩ := hM (2 * R) (by omega)
    obtain ⟨y2, z2, hR2, hy2, hz2⟩ := exists_reachIn_of_hasOpenCrossing_one hr2
    obtain ⟨w1, hq1, hr1⟩ := exists_reachIn_of_crossing hQ hyz (xa := R + 1) (xb := 2 * R)
      (ya := 0) (yb := R) (fun w hw => by simp only [Set.mem_setOf_eq] at hw; constructor <;> omega)
      (fun w hw => by simp only [Set.mem_setOf_eq] at hw; constructor <;> omega)
      (by omega) (by omega) hy hz
    obtain ⟨w2, hq2, hr2'⟩ := exists_reachIn_of_crossing hQ hR2 (xa := 2 * R + 1) (xb := 4 * R)
      (ya := 0) (yb := R) (fun w hw => by simp only [Set.mem_setOf_eq] at hw; constructor <;> omega)
      (fun w hw => by simp only [Set.mem_setOf_eq] at hw; constructor <;> omega)
      (by omega) (by omega) (by omega) (by omega)
    obtain ⟨w, hw, hw0⟩ := ih (2 * R) (by omega) (by omega) y2 z2
      (hR2.mono fun w hw => by simp only [Set.mem_setOf_eq] at hw ⊢; constructor <;> omega)
      (by omega) (by omega)
    refine ⟨w, hr1.reachable.trans (hq1.reachable.symm.trans
      (hq2.reachable.trans (hr2'.reachable.symm.trans hw))), ?_⟩
    rw [pow_succ]
    push_cast at hw0
    linarith

/-! ### The loop around the annulus -/

/-- A vertex with a coordinate of absolute value in `(R, 2R]` and the other of absolute value at
most `2R` lies in `Q_{2R} \ Q_R`. -/
theorem mem_annulus {R : ℕ} {w : Vertex 2}
    (h0 : -(2 * (R : ℤ)) ≤ w 0 ∧ w 0 ≤ 2 * R) (h1 : -(2 * (R : ℤ)) ≤ w 1 ∧ w 1 ≤ 2 * R)
    (h : w 0 ≤ -(R : ℤ) - 1 ∨ (R : ℤ) + 1 ≤ w 0 ∨ w 1 ≤ -(R : ℤ) - 1 ∨ (R : ℤ) + 1 ≤ w 1) :
    w ∈ cube (2 * R) \ cube R := by
  simp only [cube, Set.mem_sdiff, Set.mem_setOf_eq, Fin.forall_fin_two, abs_le, not_and_or,
    not_le]
  push_cast
  omega

/-- Four open arcs in the bottom, right, top and left rectangles of the annulus, whose start is
joined to vertices with arbitrarily large first coordinate, form a loop of the unique infinite
cluster in `Q_{2R} \ Q_R` with winding number `1`. -/
theorem exists_loop_of_arcs (h : HasUniqueInfiniteOpenComponent ω) {R : ℕ} (hR : 1 ≤ R)
    {p1 p2 p3 p4 : Vertex 2} (W1 : (openGraph ω).Walk p1 p2) (W2 : (openGraph ω).Walk p2 p3)
    (W3 : (openGraph ω).Walk p3 p4) (W4 : (openGraph ω).Walk p4 p1)
    (h1 : ∀ w ∈ W1.support, (-(2 * (R : ℤ)) ≤ w 0 ∧ w 0 ≤ 2 * R) ∧
      -(2 * (R : ℤ)) ≤ w 1 ∧ w 1 ≤ -(R : ℤ) - 1)
    (h2 : ∀ w ∈ W2.support, ((R : ℤ) + 1 ≤ w 0 ∧ w 0 ≤ 2 * R) ∧
      -(2 * (R : ℤ)) ≤ w 1 ∧ w 1 ≤ 2 * R)
    (h3 : ∀ w ∈ W3.support, (-(2 * (R : ℤ)) ≤ w 0 ∧ w 0 ≤ 2 * R) ∧
      (R : ℤ) + 1 ≤ w 1 ∧ w 1 ≤ 2 * R)
    (h4 : ∀ w ∈ W4.support, (-(2 * (R : ℤ)) ≤ w 0 ∧ w 0 ≤ -(R : ℤ) - 1) ∧
      -(2 * (R : ℤ)) ≤ w 1 ∧ w 1 ≤ 2 * R)
    (hesc : Escapes ω p1) :
    ∃ n : ℕ, ∃ γ : Fin (n + 1) → uniqueInfiniteComponent h,
      (∀ i, (componentGraph _).Adj (γ i) (γ (i + 1))) ∧
      (∀ i, (γ i).val ∈ cube (2 * R) \ cube R) ∧ windingNumber (fun i => (γ i).val) ≠ 0 := by
  have key := sum_darts_arg_four_arcs W1 W2 W3 W4 (fun w hw => by have := h1 w hw; omega)
    (fun w hw => by have := h2 w hw; omega) (fun w hw => by have := h3 w hw; omega)
    (fun w hw => by have := h4 w hw; omega)
  have hlen : 1 ≤ W1.length := by
    rcases Nat.eq_zero_or_pos W1.length with h0 | h0
    · have he := SimpleGraph.Walk.eq_of_length_eq_zero h0
      have := (h1 p1 W1.start_mem_support).2.2
      have := (h2 p2 W2.start_mem_support).1.1
      have := (h4 p1 W4.end_mem_support).1.2
      rw [he] at this
      omega
    · exact h0
  have hann : ∀ w ∈ (W1.append (W2.append (W3.append W4))).support,
      w ∈ cube (2 * R) \ cube R := by
    intro w hw
    simp only [SimpleGraph.Walk.mem_support_append_iff] at hw
    rcases hw with hw | hw | hw | hw
    · have := h1 w hw; exact mem_annulus (by omega) (by omega) (by omega)
    · have := h2 w hw; exact mem_annulus (by omega) (by omega) (by omega)
    · have := h3 w hw; exact mem_annulus (by omega) (by omega) (by omega)
    · have := h4 w hw; exact mem_annulus (by omega) (by omega) (by omega)
  have hlenW : 1 ≤ (W1.append (W2.append (W3.append W4))).length := by
    simp only [SimpleGraph.Walk.length_append]
    omega
  generalize W1.append (W2.append (W3.append W4)) = W at key hann hlenW
  have hmemC : ∀ w ∈ W.support, w ∈ uniqueInfiniteComponent h := fun w hw =>
    mem_uniqueInfiniteComponent_of_escapes h (hesc.of_reachable (W.takeUntil w hw).reachable)
  obtain ⟨n, hn⟩ : ∃ n, W.length = n + 1 := ⟨W.length - 1, by omega⟩
  refine ⟨n, fun i => ⟨W.getVert i, hmemC _ (W.getVert_mem_support _)⟩, fun i => ?_,
    fun i => hann _ (W.getVert_mem_support _), ?_⟩
  · rw [SimpleGraph.ConnectedComponent.toSimpleGraph_adj]
    rw [getVert_fin_succ W hn i]
    exact W.adj_getVert_succ (by omega)
  · unfold windingNumber
    have hsum := sum_fin_getVert W hn (fun a b => Complex.arg (toComplex b / toComplex a))
    dsimp only at hsum ⊢
    rw [hsum, key, div_self (by positivity)]
    exact one_ne_zero

/-- **Step `step:5.14-planarity`** of Lemma 5.14: if the crossings `AnnulusCrossings ω R` occur at
every scale `R ≥ M`, then for every `R ≥ M + 1` the unique infinite cluster contains a loop in
`Q_{2R} \ Q_R` with winding number `1` around the origin. -/
theorem loopFromCrossingsStep : LoopFromCrossingsStep := by
  intro ω h M hM
  refine ⟨M + 1, fun R hR => ?_⟩
  have hR1 : 1 ≤ R := by omega
  have hMR : M ≤ R := by omega
  obtain ⟨hb, ht, hl, hr, -⟩ := hM R hMR
  obtain ⟨yb, zb, hB, hyb, hzb⟩ := exists_reachIn_of_hasOpenCrossing_zero hb
  obtain ⟨yt, zt, hT, hyt, hzt⟩ := exists_reachIn_of_hasOpenCrossing_zero ht
  obtain ⟨yl, zl, hL, hyl, hzl⟩ := exists_reachIn_of_hasOpenCrossing_one hl
  obtain ⟨yr, zr, hRt, hyr, hzr⟩ := exists_reachIn_of_hasOpenCrossing_one hr
  obtain ⟨p1, hb1, hl1⟩ := exists_reachIn_of_crossing hB hL (xa := -(2 * R)) (xb := -R - 1)
    (ya := -(2 * R)) (yb := -R - 1)
    (fun w hw => by simp only [Set.mem_setOf_eq] at hw; constructor <;> omega)
    (fun w hw => by simp only [Set.mem_setOf_eq] at hw; constructor <;> omega)
    (by omega) (by omega) (by omega) (by omega)
  obtain ⟨p2, hb2, hr2⟩ := exists_reachIn_of_crossing hB hRt (xa := R + 1) (xb := 2 * R)
    (ya := -(2 * R)) (yb := -R - 1)
    (fun w hw => by simp only [Set.mem_setOf_eq] at hw; constructor <;> omega)
    (fun w hw => by simp only [Set.mem_setOf_eq] at hw; constructor <;> omega)
    (by omega) (by omega) (by omega) (by omega)
  obtain ⟨p3, ht3, hr3⟩ := exists_reachIn_of_crossing hT hRt (xa := R + 1) (xb := 2 * R)
    (ya := R + 1) (yb := 2 * R)
    (fun w hw => by simp only [Set.mem_setOf_eq] at hw; constructor <;> omega)
    (fun w hw => by simp only [Set.mem_setOf_eq] at hw; constructor <;> omega)
    (by omega) (by omega) (by omega) (by omega)
  obtain ⟨p4, ht4, hl4⟩ := exists_reachIn_of_crossing hT hL (xa := -(2 * R)) (xb := -R - 1)
    (ya := R + 1) (yb := 2 * R)
    (fun w hw => by simp only [Set.mem_setOf_eq] at hw; constructor <;> omega)
    (fun w hw => by simp only [Set.mem_setOf_eq] at hw; constructor <;> omega)
    (by omega) (by omega) (by omega) (by omega)
  have hesc : Escapes ω p1 := by
    intro N
    obtain ⟨w, hw, hw0⟩ := exists_reachable_of_annulusCrossings hM N.toNat R hMR hR1 yr zr
      (hRt.mono fun w hw => by simp only [Set.mem_setOf_eq] at hw ⊢; constructor <;> omega)
      (by omega) (by omega)
    refine ⟨w, (hb1.symm.trans hb2).reachable.trans (hr2.reachable.symm.trans hw), ?_⟩
    have h2k : (N.toNat : ℤ) < 2 ^ N.toNat := by exact_mod_cast Nat.lt_two_pow_self
    have hR' : (2 : ℤ) ^ N.toNat ≤ 2 ^ N.toNat * R :=
      le_mul_of_one_le_right (by positivity) (by exact_mod_cast hR1)
    have := Int.self_le_toNat N
    linarith
  obtain ⟨W1, hW1⟩ := hb1.symm.trans hb2
  obtain ⟨W2, hW2⟩ := hr2.symm.trans hr3
  obtain ⟨W3, hW3⟩ := ht3.symm.trans ht4
  obtain ⟨W4, hW4⟩ := hl4.symm.trans hl1
  refine exists_loop_of_arcs h hR1 W1 W2 W3 W4 (fun w hw => ?_) (fun w hw => ?_)
    (fun w hw => ?_) (fun w hw => ?_) hesc
  · have := hW1 w hw; simp only [Set.mem_setOf_eq] at this; omega
  · have := hW2 w hw; simp only [Set.mem_setOf_eq] at this; omega
  · have := hW3 w hw; simp only [Set.mem_setOf_eq] at this; omega
  · have := hW4 w hw; simp only [Set.mem_setOf_eq] at this; omega

/-- **Lemma 5.14** (`lemma:loops-around-annuli`): for `p > p_c(2)`, almost surely there is a scale
`M` such that for every `R ≥ M` the unique infinite cluster contains a loop in `Q_{2R} \ Q_R` with
nonzero winding number around the origin. Inputs: Kesten's crossing estimate (Theorem 11.1) and
the almost sure uniqueness of the infinite cluster. -/
theorem loopsAroundAnnuli {p : unitInterval} (hK : KestenRectangleCrossing)
    (hpc : criticalProbability 2 < (p : ℝ)) (hU : UniqueClusterAe p) :
    LoopsAroundAnnuliStmt p :=
  loopsAroundAnnuli_of_steps hK hpc hU crossingProbabilityStep borelCantelliStep
    loopFromCrossingsStep

end Rigidity.Proofs.Section5
