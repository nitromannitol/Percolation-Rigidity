import Rigidity.Steps.S3.CompareDifferentPlanes
import LatticeProb.Prob.Percolation.RootedHarmonicMeasurable

/-!
# Lemma 3.3: the Laplacian of the Green dipole correction

Step `step:3.3-green-laplacian` of Lemma 3.3 (paper L903-907 of the corrected draft). Let `B` be a
finite set of open bonds with endpoints in a cluster `C`, and `C'` a cluster with the same vertices
after the bonds of `B` are closed. All three Laplacians are literal neighbor sums of the open graph
of `ω` at a vertex of `C`.

* Closing the bonds of `B` removes from the neighbor sum at `z` exactly the increments across the
  bonds of `B` incident to `z`: `Δ_C w (z) = Δ_{C'} w (z) + ∑_{e ∈ B} (increment of w across e
  seen from z)`.
* For a bond `e = {x, y}` with endpoints in `C`, `Δ_C ∇_y G(·, e) = δ_y - δ_x` because each Green
  column has Laplacian `-δ` at its pole, so the dipole `∇_y G(·, e) (w(y) - w(x))` has Laplacian
  the negative of the increment of `w` across `e`.

For a harmonic function `ℓ'` on `C'`, the two contributions cancel.
-/

namespace Rigidity.Proofs.S3

open LatticeProb.Percolation Rigidity.Section3 Rigidity.Steps.S3

variable {d : ℕ}

namespace GreenLaplacian

/-- The increment of `f` across the edge `e` seen from the vertex `z`: `f(y) - f(z)` if
`e = {z, y}`, and zero if `z` is not an endpoint of `e`. It is the contribution of `e` to the
neighbor sum of the Laplacian of `f` at `z`. -/
noncomputable def edgeIncrement (f : Vertex d → ℝ) (z : Vertex d) : Sym2 (Vertex d) → ℝ :=
  Sym2.lift ⟨fun a b => (if z = a then f b - f a else 0) + (if z = b then f a - f b else 0),
    fun _ _ => add_comm _ _⟩

/-- An edge not incident to `z` does not contribute to the Laplacian at `z`. -/
theorem edgeIncrement_eq_zero_of_not_mem (f : Vertex d → ℝ) {z : Vertex d}
    {s : Sym2 (Vertex d)} (hz : z ∉ s) : edgeIncrement f z s = 0 := by
  induction s using Sym2.ind with
  | h a b =>
    rw [Sym2.mem_iff, not_or] at hz
    simp [edgeIncrement, hz.1, hz.2]

/-- The Laplacian of a function plus a finite family of functions. -/
theorem laplacian_add_sum {V ι : Type*} (G : SimpleGraph V) [G.LocallyFinite] (B : Finset ι)
    (f : V → ℝ) (D : ι → V → ℝ) (x : V) :
    LatticeProb.Graph.laplacian G (fun v => f v + ∑ i ∈ B, D i v) x =
      LatticeProb.Graph.laplacian G f x + ∑ i ∈ B, LatticeProb.Graph.laplacian G (D i) x := by
  unfold LatticeProb.Graph.laplacian
  calc
    ∑ y ∈ G.neighborFinset x, ((f y + ∑ i ∈ B, D i y) - (f x + ∑ i ∈ B, D i x)) =
        ∑ y ∈ G.neighborFinset x, ((f y - f x) + ∑ i ∈ B, (D i y - D i x)) := by
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Finset.sum_sub_distrib]
      ring
    _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_comm]

/-- Closing the open bonds of `B` removes from the Laplacian at `z` exactly the increments across
the bonds of `B` incident to `z`. -/
theorem laplacian_eq_closeBonds_add (ω : Configuration d) (B : Finset (Bond d))
    (hB : ∀ e ∈ B, ω e = true) (f : Vertex d → ℝ) (z : Vertex d) :
    LatticeProb.Graph.laplacian (openGraph ω) f z =
      LatticeProb.Graph.laplacian (openGraph (closeBonds B ω)) f z +
        ∑ e ∈ B, edgeIncrement f z e.val := by
  classical
  unfold LatticeProb.Graph.laplacian
  rw [← Finset.sum_filter_add_sum_filter_not ((openGraph ω).neighborFinset z)
    (fun y => ∃ e ∈ B, e.val = s(z, y))]
  refine (add_comm _ _).trans (congrArg₂ (· + ·) ?_ ?_)
  · -- the retained neighbors are the neighbors after closing `B`
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext y
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨⟨h, ho⟩, hnot⟩
      refine ⟨h, ?_⟩
      unfold closeBonds
      rw [if_neg (fun hb => hnot ⟨_, hb, rfl⟩), ho]
    · rintro ⟨h, ho⟩
      unfold closeBonds at ho
      by_cases hb : bondOfAdjacent h ∈ B
      · rw [if_pos hb] at ho
        exact absurd ho Bool.false_ne_true
      · rw [if_neg hb] at ho
        refine ⟨⟨h, ho⟩, ?_⟩
        rintro ⟨e, he, hev⟩
        exact hb (by rwa [show e = bondOfAdjacent h from Subtype.ext hev] at he)
  · -- the removed neighbors are the far endpoints of the bonds of `B` at `z`
    rw [← Finset.sum_filter_of_ne (p := fun e : Bond d => z ∈ e.val)
      fun e _ hne => by_contra fun hz => hne (edgeIncrement_eq_zero_of_not_mem f hz)]
    refine Finset.sum_bij
      (fun y hy => bondOfAdjacent (openGraph_le ω
        ((SimpleGraph.mem_neighborFinset _ _ _).mp (Finset.mem_filter.mp hy).1))) ?_ ?_ ?_ ?_
    · intro y hy
      obtain ⟨e, he, hev⟩ := (Finset.mem_filter.mp hy).2
      refine Finset.mem_filter.mpr ⟨?_, Sym2.mem_mk_left z y⟩
      rwa [show e = bondOfAdjacent _ from Subtype.ext hev] at he
    · intro y₁ _ y₂ _ h
      exact Sym2.congr_right.mp (congrArg Subtype.val h)
    · intro e he
      obtain ⟨heB, hz⟩ := Finset.mem_filter.mp he
      obtain ⟨y, hy⟩ := Sym2.mem_iff_exists.mp hz
      obtain ⟨a, b, hab, hl1⟩ := e.property
      have hadj : (nearestNeighborGraph d).Adj z y := by
        rw [← SimpleGraph.mem_edgeSet, ← hy, hab, SimpleGraph.mem_edgeSet]
        exact lattice_adj_iff_l1Dist.mpr hl1
      have heq : bondOfAdjacent hadj = e := Subtype.ext hy.symm
      refine ⟨y, Finset.mem_filter.mpr ⟨(SimpleGraph.mem_neighborFinset _ _ _).mpr
        ⟨hadj, by rw [heq]; exact hB e heB⟩, ⟨e, heB, hy⟩⟩, heq⟩
    · intro y hy
      have hne : z ≠ y := (openGraph_le ω
        ((SimpleGraph.mem_neighborFinset _ _ _).mp (Finset.mem_filter.mp hy).1)).ne
      simp [bondOfAdjacent, edgeIncrement, hne]

/-- The Laplacian on `C` of the Green function with pole `a ∈ C` is `-δ_a`. -/
theorem laplacian_greenFunction {hd : 2 ≤ d} {ω : Configuration d} (C : OpenComponent ω)
    (G : C → C → ℝ) (hG : ∀ y, IsGreenColumn d hd C y (G y)) {a : Vertex d} (ha : a ∈ C.supp)
    (z : C) :
    LatticeProb.Graph.laplacian (openGraph ω) (greenFunction C G a) z.val =
      -(if z.val = a then 1 else 0) := by
  rw [← componentLaplacian_restrict_eq C (greenFunction C G a) z]
  have hfun : (fun y : C => greenFunction C G a y.val) = G ⟨a, ha⟩ := by
    funext y
    simp [greenFunction, extend, ha]
  rw [hfun]
  have h := (hG ⟨a, ha⟩).1 z
  by_cases hz : z.val = a
  · rw [if_pos (Subtype.ext hz)] at h
    rw [if_pos hz]
    linarith
  · rw [if_neg fun h' => hz (congrArg Subtype.val h')] at h
    rw [if_neg hz]
    linarith

/-- The Green dipole `∇_y G(·, e) (w(y) - w(x))` of an edge `e = {x, y}` with endpoints in `C` has
Laplacian on `C` the negative of the increment of `w` across `e`. -/
theorem laplacian_greenDipole {hd : 2 ≤ d} {ω : Configuration d} (C : OpenComponent ω)
    (G : C → C → ℝ) (hG : ∀ y, IsGreenColumn d hd C y (G y)) (w : Vertex d → ℝ)
    (s : Sym2 (Vertex d)) (hs : ∀ v ∈ s, v ∈ C.supp) (z : C) :
    LatticeProb.Graph.laplacian (openGraph ω) (fun v => greenDipole (greenFunction C G) w v s)
      z.val = -edgeIncrement w z.val s := by
  induction s using Sym2.ind with
  | h a b =>
    have ha := laplacian_greenFunction C G hG (hs a (Sym2.mem_mk_left a b)) z
    have hb := laplacian_greenFunction C G hG (hs b (Sym2.mem_mk_right a b)) z
    have hlin : LatticeProb.Graph.laplacian (openGraph ω)
        (fun v => greenDipole (greenFunction C G) w v s(a, b)) z.val =
        (LatticeProb.Graph.laplacian (openGraph ω) (greenFunction C G a) z.val -
          LatticeProb.Graph.laplacian (openGraph ω) (greenFunction C G b) z.val) *
          (w b - w a) := by
      unfold LatticeProb.Graph.laplacian
      rw [← Finset.sum_sub_distrib, Finset.sum_mul]
      refine Finset.sum_congr rfl fun y _ => ?_
      simp only [greenDipole, Sym2.lift_mk]
      ring
    rw [hlin, ha, hb]
    simp only [edgeIncrement, Sym2.lift_mk]
    split_ifs <;> ring

end GreenLaplacian

open GreenLaplacian in
/-- Step `step:3.3-green-laplacian` (paper L903-907): for a finite set `B` of open bonds with
endpoints in a cluster `C`, a cluster `C'` with the same vertices after closing `B`, a harmonic
function `ℓ'` on `C'` and a family `G` of Green columns on `C`, the function
`ℓ' + ∑_{e ∈ B} ∇_y G(·, e) (ℓ'(y) - ℓ'(x))` is harmonic on `C`. -/
theorem greenLaplacianStep (hd : 2 ≤ d) : GreenLaplacianStep d hd := by
  intro ω C B hB C' hsupp u' hu' G hG z
  refine (componentLaplacian_restrict_eq C (fun v => extend C' u' v +
    ∑ e ∈ B, greenDipole (greenFunction C G) (extend C' u') v e.val) z).trans ?_
  rw [laplacian_add_sum, laplacian_eq_closeBonds_add ω B (fun e he => (hB e he).1)]
  have hz' : z.val ∈ C'.supp := hsupp ▸ z.property
  have hharm : LatticeProb.Graph.laplacian (openGraph (closeBonds B ω)) (extend C' u') z.val =
      0 := by
    rw [← componentLaplacian_restrict_eq C' (extend C' u') ⟨z.val, hz'⟩]
    have hfun : (fun y : C' => extend C' u' y.val) = u' := by
      funext y
      simp [extend]
    rw [hfun]
    exact hu' _
  rw [hharm, Finset.sum_congr rfl fun e he =>
    laplacian_greenDipole C G hG (extend C' u') e.val (hB e he).2 z, Finset.sum_neg_distrib]
  ring

end Rigidity.Proofs.S3
