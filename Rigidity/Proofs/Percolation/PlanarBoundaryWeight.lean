import Rigidity.Proofs.Percolation.PlanarNablaAffineBound
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The boundary weight is concentrated near the boundary

The boundary weight `W_∂(a)` counts boundary vertices `x` of `U` whose window contains `a`; the
window lies in the square `N_x` of side `9 s_x` around the partition cube of `x`. Two such squares
`N_x` and `N_{x'}` intersect only if `|x - x'|_∞ ≤ 5 (s_x + s_{x'})`, and then their intersection
has at most `81 s_x s_{x'}` vertices. Bounding the indicator of `|x - x'|_∞ ≤ 10 max(s_x, s_{x'})`
by `(10 max(s_x, s_{x'}) / max(|x - x'|_∞, 1)) ^ 2` and summing `1 / max(d, 1) ^ 2` along the faces
gives `∑_{a ∈ C_*(U)} W_∂(a) ^ 2 ≤ 324000 ∑_{x ∈ ∂U} s_x ^ 4`, a sum over the `4L` boundary vertices
(counted once per face).
-/

open LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped Classical

namespace Rigidity.Percolation

variable {ω : Configuration 2}

/-- The boundary vertices of `U`, indexed by face: `(i, true, x)` for `x` on the upper face in
direction `i` and `(i, false, x)` for the lower face. -/
noncomputable def boundaryIndex (U : TriadicCube 2) : Finset (Fin 2 × Bool × Vertex 2) :=
  (Finset.univ ×ˢ Finset.univ ×ˢ U.toIntegerCube.vertices).filter fun k =>
    if k.2.1 then k.2.2 ∈ U.toIntegerCube.upperFace k.1
    else k.2.2 ∈ U.toIntegerCube.lowerFace k.1

theorem sum_boundaryIndex (U : TriadicCube 2) (f : Vertex 2 → ℝ) :
    ∑ k ∈ boundaryIndex U, f k.2.2 = ∑ i, (∑ x ∈ U.toIntegerCube.upperFace i, f x +
      ∑ x ∈ U.toIntegerCube.lowerFace i, f x) := by
  rw [boundaryIndex, Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_product, Fintype.sum_bool]
  simp only [if_true, Bool.false_eq_true, if_false]
  congr 1
  · rw [← Finset.sum_filter]
    congr 1
    ext x
    simp only [Finset.mem_filter, and_iff_right_iff_imp]
    exact fun hx => (Finset.mem_filter.1 hx).1
  · rw [← Finset.sum_filter]
    congr 1
    ext x
    simp only [Finset.mem_filter, and_iff_right_iff_imp]
    exact fun hx => (Finset.mem_filter.1 hx).1

theorem mem_vertices_of_mem_boundaryIndex {U : TriadicCube 2} {k : Fin 2 × Bool × Vertex 2}
    (hk : k ∈ boundaryIndex U) : k.2.2 ∈ U.vertices :=
  (U.mem_toIntegerCube_vertices _).1
    (Finset.mem_product.1 (Finset.mem_product.1 (Finset.mem_filter.1 hk).1).2).2

theorem mem_face_of_mem_boundaryIndex {U : TriadicCube 2} {k : Fin 2 × Bool × Vertex 2}
    (hk : k ∈ boundaryIndex U) :
    k.2.2 ∈ U.toIntegerCube.lowerFace k.1 ∨ k.2.2 ∈ U.toIntegerCube.upperFace k.1 := by
  have h := (Finset.mem_filter.1 hk).2
  split_ifs at h
  · exact Or.inr h
  · exact Or.inl h

/-- Every vertex lies in its partition cube. -/
theorem mem_planarPartCube (x : Vertex 2) : x ∈ (planarPartCube ω x).vertices := by
  unfold planarPartCube
  split_ifs with h
  · exact (Classical.choose_spec h).1
  · intro i
    change |2 * (x i - (3 : ℤ) ^ 0 * x i)| < (3 : ℤ) ^ 0
    simp

/-- The side of the partition cube of a vertex, as a real number. -/
noncomputable def partSide (ω : Configuration 2) (x : Vertex 2) : ℝ :=
  (3 : ℝ) ^ (planarPartCube ω x).scale

theorem one_le_partSide (x : Vertex 2) : 1 ≤ partSide ω x := one_le_pow₀ (by norm_num)

/-- The boundary weight is at most the number of boundary vertices whose square of side `9s`
contains the vertex. -/
theorem boundaryWeight_le_sum (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) (a : Vertex 2) :
    boundaryWeight ω U a ≤ ∑ k ∈ boundaryIndex U,
      (if a ∈ (planarPartCube ω k.2.2).ninefold.vertices then (1 : ℝ) else 0) := by
  have hmono : ∀ x ∈ U.vertices,
      (if a ∈ planarClusterWindow ω U x then (1 : ℝ) else 0) ≤
        (if a ∈ (planarPartCube ω x).ninefold.vertices then 1 else 0) := by
    intro x hx
    by_cases ha : a ∈ planarClusterWindow ω U x
    · have hw := (Finset.mem_filter.1 ha).1
      have hsub := planarPartCube_subset_of_resolved hP hU hx
      have h9 := TriadicCube.subset_ninefold_of_mem_planarSquares
        ((planarPartCube ω x).window_mem_planarSquares (hU x hx) hsub) hw
      simp [ha, h9]
    · rw [if_neg ha]
      split_ifs <;> norm_num
  calc boundaryWeight ω U a
      = ∑ k ∈ boundaryIndex U,
          (if a ∈ planarClusterWindow ω U k.2.2 then (1 : ℝ) else 0) := by
        rw [sum_boundaryIndex U (fun x => if a ∈ planarClusterWindow ω U x then 1 else 0)]
        rfl
    _ ≤ _ := Finset.sum_le_sum fun k hk => hmono _ (mem_vertices_of_mem_boundaryIndex hk)

/-- The sup distance between two vertices. -/
def supDist (x y : Vertex 2) : ℤ := max |x 0 - y 0| |x 1 - y 1|

/-- **Intersections of squares around partition cubes.** -/
theorem card_inter_ninefold_le (x x' : Vertex 2) :
    (((planarPartCube ω x).ninefold.vertices ∩ (planarPartCube ω x').ninefold.vertices).card : ℝ)
      * (max (supDist x x') 1 : ℝ) ^ 2 ≤ 8100 * (partSide ω x ^ 4 + partSide ω x' ^ 4) := by
  set Q := planarPartCube ω x
  set Q' := planarPartCube ω x'
  set ρ := partSide ω x with hρ
  set ρ' := partSide ω x' with hρ'
  have hρ1 : 1 ≤ ρ := one_le_partSide x
  have hρ1' : 1 ≤ ρ' := one_le_partSide x'
  have hcardN : ∀ R : TriadicCube 2, ((R.ninefold.vertices.card : ℕ) : ℝ) =
      81 * ((3 : ℝ) ^ R.scale) ^ 2 := by
    intro R
    rw [IntegerCube.card_vertices]
    change (((9 * 3 ^ R.scale) ^ 2 : ℕ) : ℝ) = _
    push_cast
    ring
  rcases (Q.ninefold.vertices ∩ Q'.ninefold.vertices).eq_empty_or_nonempty with he | ⟨a, ha⟩
  · rw [he, Finset.card_empty, Nat.cast_zero, zero_mul]
    positivity
  have hcard : ((Q.ninefold.vertices ∩ Q'.ninefold.vertices).card : ℝ) ≤ 81 * ρ * ρ' := by
    have h1 : ((Q.ninefold.vertices ∩ Q'.ninefold.vertices).card : ℝ) ≤ 81 * ρ ^ 2 := by
      rw [hρ, partSide, ← hcardN Q]
      exact_mod_cast Finset.card_le_card Finset.inter_subset_left
    have h2 : ((Q.ninefold.vertices ∩ Q'.ninefold.vertices).card : ℝ) ≤ 81 * ρ' ^ 2 := by
      rw [hρ', partSide, ← hcardN Q']
      exact_mod_cast Finset.card_le_card Finset.inter_subset_right
    rcases le_total ρ ρ' with h | h
    · nlinarith
    · nlinarith
  -- the two squares meet, so `x` and `x'` are close
  obtain ⟨ha1, ha2⟩ := Finset.mem_inter.1 ha
  have hd : (supDist x x' : ℝ) ≤ 5 * ρ + 5 * ρ' := by
    have hx : x ∈ Q.vertices := mem_planarPartCube x
    have hx' : x' ∈ Q'.vertices := mem_planarPartCube x'
    have hdist : ∀ i, |x i - x' i| ≤ 5 * 3 ^ Q.scale + 5 * 3 ^ Q'.scale := by
      intro i
      have h1 := (TriadicCube.mem_ninefold.1 (Finset.mem_coe.2 ha1)) i
      have h2 := (TriadicCube.mem_ninefold.1 (Finset.mem_coe.2 ha2)) i
      have h3 := Q.abs_sub_center_le hx i
      have h4 := Q'.abs_sub_center_le hx' i
      have h5 := Q.two_mul_ninefoldRadius
      have h6 := Q'.two_mul_ninefoldRadius
      have h7 := le_abs_self (x i - Q.center i)
      have h8 := neg_abs_le (x i - Q.center i)
      have h9 := le_abs_self (x' i - Q'.center i)
      have h10 := neg_abs_le (x' i - Q'.center i)
      rw [abs_le] at h1 h2 ⊢
      constructor <;> omega
    have hmax : supDist x x' ≤ 5 * 3 ^ Q.scale + 5 * 3 ^ Q'.scale :=
      max_le (hdist 0) (hdist 1)
    have : ((supDist x x' : ℤ) : ℝ) ≤ ((5 * 3 ^ Q.scale + 5 * 3 ^ Q'.scale : ℤ) : ℝ) := by
      exact_mod_cast hmax
    push_cast at this
    rw [hρ, hρ', partSide, partSide]
    exact this
  have hm : (max (supDist x x') 1 : ℝ) ≤ 5 * ρ + 5 * ρ' := max_le hd (by linarith)
  have hm0 : (0 : ℝ) ≤ (max (supDist x x') 1 : ℝ) := le_trans zero_le_one (le_max_right _ _)
  have hsq : (max (supDist x x') 1 : ℝ) ^ 2 ≤ (5 * ρ + 5 * ρ') ^ 2 :=
    pow_le_pow_left₀ hm0 hm 2
  have hcard0 : (0 : ℝ) ≤ ((Q.ninefold.vertices ∩ Q'.ninefold.vertices).card : ℝ) :=
    Nat.cast_nonneg _
  calc ((Q.ninefold.vertices ∩ Q'.ninefold.vertices).card : ℝ) *
        (max (supDist x x') 1 : ℝ) ^ 2
      ≤ (81 * ρ * ρ') * (5 * ρ + 5 * ρ') ^ 2 :=
        mul_le_mul hcard hsq (by positivity) (by positivity)
    _ ≤ 8100 * (ρ ^ 4 + ρ' ^ 4) := by
        nlinarith [sq_nonneg (ρ - ρ'), sq_nonneg (ρ + ρ'), mul_pos (by linarith : (0 : ℝ) < ρ)
          (by linarith : (0 : ℝ) < ρ'), sq_nonneg (ρ ^ 2 - ρ' ^ 2)]

theorem supDist_comm (x y : Vertex 2) : supDist x y = supDist y x := by
  unfold supDist
  rw [abs_sub_comm (x 0), abs_sub_comm (x 1)]

/-- The summable profile `z ↦ 1 / max(|z|, 1) ^ 2` on the integers. -/
noncomputable def invSqProfile (z : ℤ) : ℝ := 1 / (max (|(z : ℝ)|) 1) ^ 2

theorem invSqProfile_nonneg (z : ℤ) : 0 ≤ invSqProfile z := by
  unfold invSqProfile
  positivity

theorem hasSum_invSqProfile : HasSum invSqProfile (Real.pi ^ 2 / 6 + 1 + Real.pi ^ 2 / 6) := by
  have h1 : HasSum (fun n : ℕ => invSqProfile n) (Real.pi ^ 2 / 6 + 1) := by
    have h := hasSum_zeta_two.add (hasSum_ite_eq (0 : ℕ) (1 : ℝ))
    refine (funext fun n => ?_ : (fun n : ℕ => invSqProfile n) = _) ▸ h
    unfold invSqProfile
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      rw [if_neg (Nat.pos_iff_ne_zero.1 hn), add_zero, Int.cast_natCast,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ n), max_eq_left hn']
  have h2 : HasSum (fun n : ℕ => invSqProfile (-(n + 1 : ℤ))) (Real.pi ^ 2 / 6) := by
    have h := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
    simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero, sub_zero] at h
    refine (funext fun n => ?_ : (fun n : ℕ => invSqProfile (-(n + 1 : ℤ))) = _) ▸ h
    unfold invSqProfile
    have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    push_cast
    rw [abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1), max_eq_left hn]
  exact h1.of_nat_of_neg_add_one h2

/-- Sums of the profile over finite sets of integers are at most `5`. -/
theorem sum_invSqProfile_le (S : Finset ℤ) : ∑ z ∈ S, invSqProfile z ≤ 5 := by
  refine (sum_le_hasSum S (fun z _ => invSqProfile_nonneg z) hasSum_invSqProfile).trans ?_
  have := Real.pi_lt_d2
  have h0 := Real.pi_pos
  nlinarith

theorem abs_sub_le_supDist (x y : Vertex 2) (j : Fin 2) : |x j - y j| ≤ supDist x y := by
  unfold supDist
  fin_cases j
  · exact le_max_left _ _
  · exact le_max_right _ _

/-- **Sums along a face.** -/
theorem sum_face_invSq_le (U : TriadicCube 2) (i : Fin 2) (b : Bool) (x : Vertex 2) :
    ∑ x' ∈ (if b then U.toIntegerCube.upperFace i else U.toIntegerCube.lowerFace i),
      1 / (max (supDist x x' : ℝ) 1) ^ 2 ≤ 5 := by
  set F := if b then U.toIntegerCube.upperFace i else U.toIntegerCube.lowerFace i with hF
  set j := i.rev
  have hcoord : ∀ l : Fin 2, l = i ∨ l = j := by
    intro l
    fin_cases i <;> fin_cases l <;> simp [j]
  have hconst : ∀ x' ∈ F, ∀ x'' ∈ F, x' i = x'' i := by
    intro x' hx' x'' hx''
    rw [hF] at hx' hx''
    split_ifs at hx' hx'' <;>
      · have h1 := (Finset.mem_filter.1 hx').2
        have h2 := (Finset.mem_filter.1 hx'').2
        omega
  have hinj : Set.InjOn (fun x' : Vertex 2 => x' j) ↑F := by
    intro x' hx' x'' hx'' h
    funext l
    rcases hcoord l with rfl | rfl
    · exact hconst x' hx' x'' hx''
    · exact h
  have hle : ∀ x' ∈ F, 1 / (max (supDist x x' : ℝ) 1) ^ 2 ≤ invSqProfile (x j - x' j) := by
    intro x' _
    unfold invSqProfile
    have hd : |((x j - x' j : ℤ) : ℝ)| ≤ (supDist x x' : ℝ) := by
      rw [← Int.cast_abs]
      exact_mod_cast abs_sub_le_supDist x x' j
    have hpos : (0 : ℝ) < max (|((x j - x' j : ℤ) : ℝ)|) 1 := lt_max_of_lt_right one_pos
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_left₀ hpos.le (max_le_max hd le_rfl) 2
  calc ∑ x' ∈ F, 1 / (max (supDist x x' : ℝ) 1) ^ 2
      ≤ ∑ x' ∈ F, invSqProfile (x j - x' j) := Finset.sum_le_sum hle
    _ = ∑ t ∈ F.image (fun x' : Vertex 2 => x' j), invSqProfile (x j - t) :=
        (Finset.sum_image (f := fun t => invSqProfile (x j - t)) hinj).symm
    _ = ∑ z ∈ (F.image (fun x' : Vertex 2 => x' j)).image (fun t => x j - t),
          invSqProfile z :=
        (Finset.sum_image fun t _ t' _ h => by simpa using h).symm
    _ ≤ 5 := sum_invSqProfile_le _

/-- **Sums along the boundary.** -/
theorem sum_boundaryIndex_invSq_le (U : TriadicCube 2) (x : Vertex 2) :
    ∑ k ∈ boundaryIndex U, 1 / (max (supDist x k.2.2 : ℝ) 1) ^ 2 ≤ 20 := by
  rw [sum_boundaryIndex U (fun x' => 1 / (max (supDist x x' : ℝ) 1) ^ 2)]
  have h1 := fun i => sum_face_invSq_le U i true x
  have h2 := fun i => sum_face_invSq_le U i false x
  simp only [if_true, Bool.false_eq_true, if_false] at h1 h2
  calc ∑ i, (∑ x' ∈ U.toIntegerCube.upperFace i, 1 / (max (supDist x x' : ℝ) 1) ^ 2 +
        ∑ x' ∈ U.toIntegerCube.lowerFace i, 1 / (max (supDist x x' : ℝ) 1) ^ 2)
      ≤ ∑ _i : Fin 2, (5 + 5 : ℝ) := Finset.sum_le_sum fun i _ => add_le_add (h1 i) (h2 i)
    _ = 20 := by norm_num

/-- Symmetric double sums against a summable kernel. -/
theorem sum_sum_add_div_le {ι : Type*} (I : Finset ι) (a : ι → ℝ) (m : ι → ι → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hsymm : ∀ k k', m k k' = m k' k) (C : ℝ)
    (hC : ∀ k ∈ I, ∑ k' ∈ I, 1 / m k k' ≤ C) :
    ∑ k ∈ I, ∑ k' ∈ I, (a k + a k') / m k k' ≤ 2 * C * ∑ k ∈ I, a k := by
  have e1 : ∑ k ∈ I, ∑ k' ∈ I, (a k + a k') / m k k' =
      ∑ k ∈ I, a k * ∑ k' ∈ I, 1 / m k k' + ∑ k ∈ I, a k * ∑ k' ∈ I, 1 / m k k' := by
    calc ∑ k ∈ I, ∑ k' ∈ I, (a k + a k') / m k k'
        = ∑ k ∈ I, ∑ k' ∈ I, a k / m k k' + ∑ k ∈ I, ∑ k' ∈ I, a k' / m k k' := by
          simp only [add_div, Finset.sum_add_distrib]
      _ = _ := by
          congr 1
          · refine Finset.sum_congr rfl fun k _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun k' _ => ?_
            ring
          · rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun k' _ => ?_
            rw [hsymm]
            ring
  rw [e1]
  have h1 : ∑ k ∈ I, a k * ∑ k' ∈ I, 1 / m k k' ≤ ∑ k ∈ I, a k * C :=
    Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left (hC k hk) (ha k)
  rw [← Finset.sum_mul] at h1
  linarith

/-- Expansion of the squared boundary weight into intersections of squares. -/
theorem sum_sq_boundaryWeight_le_card (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) :
    ∑ x : ↥(clusterVertices ω U), boundaryWeight ω U x.1 ^ 2 ≤
      ∑ k ∈ boundaryIndex U, ∑ k' ∈ boundaryIndex U,
        (((planarPartCube ω k.2.2).ninefold.vertices ∩
          (planarPartCube ω k'.2.2).ninefold.vertices).card : ℝ) := by
  set I := boundaryIndex U
  have hstep : ∀ x : ↥(clusterVertices ω U), boundaryWeight ω U x.1 ^ 2 ≤
      ∑ k ∈ I, ∑ k' ∈ I, (if x.1 ∈ (planarPartCube ω k.2.2).ninefold.vertices ∩
        (planarPartCube ω k'.2.2).ninefold.vertices then (1 : ℝ) else 0) := by
    intro x
    refine (pow_le_pow_left₀ (boundaryWeight_nonneg U x.1)
      (boundaryWeight_le_sum hP hU x.1) 2).trans (le_of_eq ?_)
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => ?_
    by_cases h1 : x.1 ∈ (planarPartCube ω k.2.2).ninefold.vertices <;>
      by_cases h2 : x.1 ∈ (planarPartCube ω k'.2.2).ninefold.vertices <;>
      simp [h1, h2]
  calc ∑ x : ↥(clusterVertices ω U), boundaryWeight ω U x.1 ^ 2
      ≤ ∑ x : ↥(clusterVertices ω U), ∑ k ∈ I, ∑ k' ∈ I,
          (if x.1 ∈ (planarPartCube ω k.2.2).ninefold.vertices ∩
            (planarPartCube ω k'.2.2).ninefold.vertices then (1 : ℝ) else 0) :=
        Finset.sum_le_sum fun x _ => hstep x
    _ = ∑ k ∈ I, ∑ k' ∈ I, ∑ x : ↥(clusterVertices ω U),
          (if x.1 ∈ (planarPartCube ω k.2.2).ninefold.vertices ∩
            (planarPartCube ω k'.2.2).ninefold.vertices then (1 : ℝ) else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_comm]
    _ ≤ _ := by
        refine Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun k' _ => ?_
        rw [Finset.sum_coe_sort (clusterVertices ω U)
          (fun a => if a ∈ (planarPartCube ω k.2.2).ninefold.vertices ∩
            (planarPartCube ω k'.2.2).ninefold.vertices then (1 : ℝ) else 0),
          Finset.sum_boole]
        exact_mod_cast Finset.card_le_card fun a ha => (Finset.mem_filter.1 ha).2

/-- **The boundary weight is concentrated near the boundary.** -/
theorem sum_sq_boundaryWeight_le (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) :
    ∑ x : ↥(clusterVertices ω U), boundaryWeight ω U x.1 ^ 2 ≤
      324000 * ∑ k ∈ boundaryIndex U, partSide ω k.2.2 ^ 4 := by
  have hm_pos : ∀ k k' : Fin 2 × Bool × Vertex 2,
      0 < (max (supDist k.2.2 k'.2.2 : ℝ) 1) ^ 2 :=
    fun k k' => pow_pos (lt_max_of_lt_right one_pos) 2
  have h2 : ∀ k k' : Fin 2 × Bool × Vertex 2,
      (((planarPartCube ω k.2.2).ninefold.vertices ∩
        (planarPartCube ω k'.2.2).ninefold.vertices).card : ℝ) ≤
      (8100 * partSide ω k.2.2 ^ 4 + 8100 * partSide ω k'.2.2 ^ 4) /
        (max (supDist k.2.2 k'.2.2 : ℝ) 1) ^ 2 := by
    intro k k'
    rw [le_div_iff₀ (hm_pos k k')]
    have := card_inter_ninefold_le (ω := ω) k.2.2 k'.2.2
    linarith
  have hsum := sum_sum_add_div_le (boundaryIndex U) (fun k => 8100 * partSide ω k.2.2 ^ 4)
    (fun k k' => (max (supDist k.2.2 k'.2.2 : ℝ) 1) ^ 2) (fun k => by positivity)
    (fun k k' => by simp only [supDist_comm]) 20
    (fun k _ => sum_boundaryIndex_invSq_le U k.2.2)
  calc ∑ x : ↥(clusterVertices ω U), boundaryWeight ω U x.1 ^ 2
      ≤ _ := sum_sq_boundaryWeight_le_card hP hU
    _ ≤ ∑ k ∈ boundaryIndex U, ∑ k' ∈ boundaryIndex U,
          (8100 * partSide ω k.2.2 ^ 4 + 8100 * partSide ω k'.2.2 ^ 4) /
            (max (supDist k.2.2 k'.2.2 : ℝ) 1) ^ 2 :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun k' _ => h2 k k'
    _ ≤ 2 * 20 * ∑ k ∈ boundaryIndex U, 8100 * partSide ω k.2.2 ^ 4 := hsum
    _ = 324000 * ∑ k ∈ boundaryIndex U, partSide ω k.2.2 ^ 4 := by
        rw [← Finset.mul_sum]
        ring

end Rigidity.Percolation
