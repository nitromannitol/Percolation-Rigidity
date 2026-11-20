import Rigidity.Proofs.Percolation.PlanarPartition
import Rigidity.Percolation.IntegerCubeCoalescenceScales

/-!
# Weights of the planar coarse-graining

The local coarse-graining bounds control a function on the infinite cluster by the variation of
the function over the squares of side `9s` around the partition cubes. These squares overlap, and
the overlap at a vertex `a` is controlled by the reach of the partition at `a`: the largest side
of a partition cube whose square of side `9s` contains `a`. This file proves

* the elementary power-mean bound of the variation by the `m`-th power energy of a square;
* the regrouping of a weighted sum of square energies as a sum over open edges, with weight at an
  edge given by the overlap of the squares containing it;
* the bound of the overlap by a power of the reach;
* finiteness of all moments of the reach, uniformly in the vertex, in the supercritical regime.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped ENNReal Classical

namespace Rigidity.Percolation

/-- The sum of the `m`-th powers of the increments of `w` over ordered pairs of open neighbours
inside a finite set. -/
noncomputable def edgeEnergyIn (ω : Configuration 2) (S : Finset (Vertex 2)) (w : Vertex 2 → ℝ)
    (m : ℕ) : ℝ :=
  ∑ x ∈ S, ∑ y ∈ S, if (openGraph ω).Adj x y then |w x - w y| ^ m else 0

theorem edgeEnergyIn_nonneg (ω : Configuration 2) (S : Finset (Vertex 2)) (w : Vertex 2 → ℝ)
    (m : ℕ) : 0 ≤ edgeEnergyIn ω S w m :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by
    split_ifs <;> positivity

/-- **Power-mean bound.** The `(n + 1)`-st power of the variation over a finite set is at most
`(#S ^ 2) ^ n` times the `(n + 1)`-st power energy over the set. -/
theorem edgeVariationIn_pow_le (ω : Configuration 2) (S : Finset (Vertex 2))
    (w : Vertex 2 → ℝ) (n : ℕ) :
    edgeVariationIn ω S w ^ (n + 1) ≤ ((S.card : ℝ) ^ 2) ^ n * edgeEnergyIn ω S w (n + 1) := by
  set g : Vertex 2 × Vertex 2 → ℝ := fun q =>
    if (openGraph ω).Adj q.1 q.2 then |w q.1 - w q.2| else 0 with hg
  have hg0 : ∀ q ∈ S ×ˢ S, 0 ≤ g q := fun q _ => by
    simp only [hg]
    split_ifs <;> positivity
  have h1 : edgeVariationIn ω S w = ∑ q ∈ S ×ˢ S, g q := by
    rw [Finset.sum_product]
    rfl
  have h2 : edgeEnergyIn ω S w (n + 1) = ∑ q ∈ S ×ˢ S, g q ^ (n + 1) := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    simp only [hg]
    split_ifs <;> simp
  rw [h1, h2]
  have h := pow_sum_le_card_mul_sum_pow hg0 n
  rw [Finset.card_product] at h
  push_cast at h
  calc _ ≤ _ := h
    _ = _ := by ring

/-- **Regrouping.** A weighted sum of energies over finite sets `T x`, `x ∈ X`, is at most the sum
over pairs of open neighbours of the union of the increments, each weighted by the total weight of
the sets containing its first vertex. -/
theorem sum_mul_edgeEnergyIn_le (ω : Configuration 2) (w : Vertex 2 → ℝ) (m : ℕ)
    (X : Finset (Vertex 2)) (T : Vertex 2 → Finset (Vertex 2)) (c : Vertex 2 → ℝ)
    (hc : ∀ x, 0 ≤ c x) :
    ∑ x ∈ X, c x * edgeEnergyIn ω (T x) w m ≤
      ∑ a ∈ X.biUnion T, ∑ b ∈ X.biUnion T,
        (if (openGraph ω).Adj a b then |w a - w b| ^ m else 0) *
          ∑ x ∈ X, if a ∈ T x then c x else 0 := by
  set B := X.biUnion T
  set g : Vertex 2 → Vertex 2 → ℝ := fun a b =>
    if (openGraph ω).Adj a b then |w a - w b| ^ m else 0 with hg
  have hg0 : ∀ a b, 0 ≤ g a b := fun a b => by
    simp only [hg]
    split_ifs <;> positivity
  have hstep : ∀ x ∈ X, edgeEnergyIn ω (T x) w m ≤
      ∑ a ∈ B, if a ∈ T x then ∑ b ∈ B, g a b else 0 := by
    intro x hx
    have hTB : T x ⊆ B := Finset.subset_biUnion_of_mem T hx
    rw [← Finset.sum_filter]
    have hfil : B.filter (fun a => a ∈ T x) = T x := by
      ext a
      simp only [Finset.mem_filter, and_iff_right_iff_imp]
      exact fun ha => hTB ha
    rw [hfil]
    exact Finset.sum_le_sum fun a _ =>
      Finset.sum_le_sum_of_subset_of_nonneg hTB fun b _ _ => hg0 a b
  calc ∑ x ∈ X, c x * edgeEnergyIn ω (T x) w m
      ≤ ∑ x ∈ X, c x * ∑ a ∈ B, (if a ∈ T x then ∑ b ∈ B, g a b else 0) :=
        Finset.sum_le_sum fun x hx => mul_le_mul_of_nonneg_left (hstep x hx) (hc x)
    _ = ∑ x ∈ X, ∑ a ∈ B, (if a ∈ T x then c x else 0) * ∑ b ∈ B, g a b := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        split_ifs <;> simp
    _ = ∑ a ∈ B, ∑ x ∈ X, (if a ∈ T x then c x else 0) * ∑ b ∈ B, g a b :=
        Finset.sum_comm
    _ = ∑ a ∈ B, ∑ b ∈ B, g a b * ∑ x ∈ X, (if a ∈ T x then c x else 0) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.sum_mul, mul_comm, Finset.sum_mul]

/-- The reach of the planar partition at a vertex: the largest side of a partition cube whose
square of side `9s` contains the vertex. -/
noncomputable def planarReach (ω : Configuration 2) (a : Vertex 2) : ℝ≥0∞ :=
  ⨆ (Q : TriadicCube 2) (_ : Q.IsMaximalStopping (planarGoodCubes ω) ∧
    a ∈ (↑Q.ninefold.vertices : Set (Vertex 2))), (3 : ℝ≥0∞) ^ Q.scale

/-- Powers of the reach are bounded by sums over the partition cubes reaching the vertex. -/
theorem planarReach_pow_le (ω : Configuration 2) (a : Vertex 2) (n : ℕ) :
    planarReach ω a ^ (n + 1) ≤
      ∑' Q : TriadicCube 2, if Q.IsMaximalStopping (planarGoodCubes ω) ∧
        a ∈ (↑Q.ninefold.vertices : Set (Vertex 2)) then (3 : ℝ≥0∞) ^ ((n + 1) * Q.scale)
        else 0 := by
  unfold planarReach
  rw [ENNReal.iSup_pow_of_ne_zero (Nat.succ_ne_zero n)]
  refine iSup_le fun Q => ?_
  rw [ENNReal.iSup_pow_of_ne_zero (Nat.succ_ne_zero n)]
  refine iSup_le fun hQ => ?_
  refine le_trans (le_of_eq ?_) (ENNReal.le_tsum Q)
  rw [if_pos hQ, ← pow_mul, mul_comm]

/-- **Overlap bound.** On the partition event, the total weight `s ^ k` of the vertices `x ∈ X`
whose partition cube has its square of side `9s` around `a` is at most `121` times the
`(k + 2)`-nd power of the reach at `a`. -/
theorem ofReal_sum_ninefold_le {ω : Configuration 2} (hP : PlanarPartitionEvent ω)
    (X : Finset (Vertex 2)) (a : Vertex 2) (k : ℕ) :
    ENNReal.ofReal (∑ x ∈ X, if a ∈ (planarPartCube ω x).ninefold.vertices then
        (3 : ℝ) ^ (k * (planarPartCube ω x).scale) else 0) ≤
      121 * planarReach ω a ^ (k + 2) := by
  by_cases hR : planarReach ω a = ∞
  · rw [hR, ENNReal.top_pow (Nat.succ_ne_zero _), ENNReal.mul_top (by norm_num)]
    exact le_top
  set r := (planarReach ω a).toReal with hr
  have hRr : planarReach ω a = ENNReal.ofReal r := (ENNReal.ofReal_toReal hR).symm
  have hle : ∀ x ∈ X, a ∈ (planarPartCube ω x).ninefold.vertices →
      (3 : ℝ) ^ (planarPartCube ω x).scale ≤ r := by
    intro x _ hax
    have h1 : (3 : ℝ≥0∞) ^ (planarPartCube ω x).scale ≤ planarReach ω a := by
      unfold planarReach
      exact le_iSup₂_of_le (planarPartCube ω x) ⟨(planarPartCube_spec hP x).2, hax⟩ le_rfl
    have h2 := ENNReal.toReal_mono hR h1
    simpa using h2
  set F := X.filter fun x => a ∈ (planarPartCube ω x).ninefold.vertices
  rw [← Finset.sum_filter]
  change ENNReal.ofReal (∑ x ∈ F, (3 : ℝ) ^ (k * (planarPartCube ω x).scale)) ≤ _
  rcases F.eq_empty_or_nonempty with hF | ⟨x0, hx0⟩
  · rw [hF, Finset.sum_empty, ENNReal.ofReal_zero]
    exact zero_le
  have hx0' := Finset.mem_filter.1 hx0
  have hr1 : 1 ≤ r := le_trans (one_le_pow₀ (by norm_num)) (hle x0 hx0'.1 hx0'.2)
  set N := ⌊5 * r⌋₊
  set Box : Finset (Vertex 2) :=
    Fintype.piFinset fun i => Finset.Icc (a i - (N : ℤ)) (a i + (N : ℤ))
  have hFB : F ⊆ Box := by
    intro x hx
    obtain ⟨hxX, hax⟩ := Finset.mem_filter.1 hx
    set Q := planarPartCube ω x
    have hs := hle x hxX hax
    have hN : ((5 * 3 ^ Q.scale : ℕ) : ℤ) ≤ (N : ℤ) := by
      have : (5 * 3 ^ Q.scale : ℕ) ≤ N := by
        apply Nat.le_floor
        push_cast
        linarith
      exact_mod_cast this
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    have h1 := Q.abs_sub_center_le (planarPartCube_spec hP x).1 i
    have h2 := (TriadicCube.mem_ninefold.1 (Finset.mem_coe.2 hax)) i
    have h3 := Q.two_mul_ninefoldRadius
    have h4 := abs_sub_le (x i) (Q.center i) (a i)
    rw [abs_sub_comm (Q.center i) (a i)] at h4
    push_cast at hN
    have h5 : |x i - a i| ≤ (N : ℤ) := by omega
    rw [abs_le] at h5
    constructor <;> omega
  have hcard : (Box.card : ℝ) ≤ 121 * r ^ 2 := by
    have hc : Box.card = (2 * N + 1) ^ 2 := by
      simp only [Box, Fintype.card_piFinset, Int.card_Icc, Fin.prod_univ_two]
      have : ∀ z : ℤ, (z + (N : ℤ) + 1 - (z - (N : ℤ))).toNat = 2 * N + 1 := by
        intro z
        omega
      rw [this, this]
      ring
    rw [hc]
    push_cast
    have hN : (N : ℝ) ≤ 5 * r := Nat.floor_le (by linarith)
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith
  have hsum : ∑ x ∈ F, (3 : ℝ) ^ (k * (planarPartCube ω x).scale) ≤ 121 * r ^ 2 * r ^ k := by
    calc ∑ x ∈ F, (3 : ℝ) ^ (k * (planarPartCube ω x).scale)
        ≤ ∑ _x ∈ F, r ^ k := by
          refine Finset.sum_le_sum fun x hx => ?_
          obtain ⟨hxX, hax⟩ := Finset.mem_filter.1 hx
          rw [mul_comm, pow_mul]
          exact pow_le_pow_left₀ (by positivity) (hle x hxX hax) k
      _ = (F.card : ℝ) * r ^ k := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Box.card : ℝ) * r ^ k := by
          gcongr
      _ ≤ 121 * r ^ 2 * r ^ k := by gcongr
  calc ENNReal.ofReal (∑ x ∈ F, (3 : ℝ) ^ (k * (planarPartCube ω x).scale))
      ≤ ENNReal.ofReal (121 * r ^ 2 * r ^ k) := ENNReal.ofReal_le_ofReal hsum
    _ = 121 * planarReach ω a ^ (k + 2) := by
        have hr0 : 0 ≤ r := ENNReal.toReal_nonneg
        rw [hRr, ← ENNReal.ofReal_pow hr0, mul_assoc, ← pow_add,
          ENNReal.ofReal_mul (by norm_num), add_comm 2 k, ENNReal.ofReal_ofNat]

end Rigidity.Percolation
