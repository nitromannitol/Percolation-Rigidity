import Rigidity.Proofs.Cluster.CoarseSobolev

/-!
# The Sobolev inequality on a square of the planar lattice

For a function `F` on the grid `{0, …, L-1}²`,
`∑_p (F(p) - (F))² ≤ (1/2) (∑ |horizontal increments| + ∑ |vertical increments|)²`,
the planar Sobolev–Poincaré inequality from `L¹` to `L²` with a constant independent of `L`. The
proof writes `∑_p (F(p) - (F))² = (2L²)⁻¹ ∑_{p,q} (F(p) - F(q))²` and bounds `|F(p) - F(q)|` by
the variation along the row of `p` and the column of `q`, and also by the variation along the
column of `p` and the row of `q`; the product of the two bounds sums to `L² (R + C)²`.
-/

open Finset LatticeProb.Percolation
open scoped Classical

namespace Rigidity.Percolation

/-- The oscillation of a sequence between two indices below `L` is at most its total variation on
`{0, …, L-1}`. -/
theorem abs_sub_le_sum_range_abs_sub (g : ℕ → ℝ) {i j L : ℕ} (hi : i < L) (hj : j < L) :
    |g i - g j| ≤ ∑ k ∈ range (L - 1), |g (k + 1) - g k| := by
  have key : ∀ a b : ℕ, a ≤ b → b < L → |g b - g a| ≤ ∑ k ∈ range (L - 1), |g (k + 1) - g k| := by
    intro a b hab hb
    have htel : g b - g a = ∑ k ∈ range (b - a), (g (a + k + 1) - g (a + k)) := by
      have h := Finset.sum_range_sub (fun k => g (a + k)) (b - a)
      simp only [add_zero, ← add_assoc] at h
      rw [h, Nat.add_sub_cancel' hab]
    rw [htel]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hmap : ∑ k ∈ range (b - a), |g (a + k + 1) - g (a + k)| =
        ∑ m ∈ (range (b - a)).map (addLeftEmbedding a), |g (m + 1) - g m| := by
      rw [Finset.sum_map]
      rfl
    rw [hmap]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => abs_nonneg _
    intro m hm
    obtain ⟨k, hk, rfl⟩ := Finset.mem_map.1 hm
    rw [Finset.mem_range] at hk ⊢
    simp only [addLeftEmbedding_apply]
    omega
  rcases le_total i j with h | h
  · rw [abs_sub_comm]
    exact key i j h hj
  · exact key j i h hi

/-- `∑_{x ∈ D} (f x - (f)_D)² = (2|D|)⁻¹ ∑_{x, y ∈ D} (f x - f y)²`. -/
theorem sum_sq_sub_mean_eq {ι : Type*} (D : Finset ι) (f : ι → ℝ) (hD : D.Nonempty) :
    ∑ x ∈ D, (f x - (∑ y ∈ D, f y) / D.card) ^ 2 =
      (∑ x ∈ D, ∑ y ∈ D, (f x - f y) ^ 2) / (2 * D.card) := by
  have hn : (D.card : ℝ) ≠ 0 := by exact_mod_cast hD.card_pos.ne'
  have h1 : ∑ x ∈ D, (f x - (∑ y ∈ D, f y) / D.card) ^ 2 =
      ∑ x ∈ D, f x ^ 2 - (∑ y ∈ D, f y) ^ 2 / D.card := by
    have e : ∀ x, (f x - (∑ y ∈ D, f y) / D.card) ^ 2 =
        f x ^ 2 - 2 * ((∑ y ∈ D, f y) / D.card) * f x + ((∑ y ∈ D, f y) / D.card) ^ 2 := by
      intro x
      ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      nsmul_eq_mul, ← Finset.mul_sum]
    field_simp
    ring
  have h2 : ∑ x ∈ D, ∑ y ∈ D, (f x - f y) ^ 2 =
      2 * D.card * ∑ x ∈ D, f x ^ 2 - 2 * (∑ y ∈ D, f y) ^ 2 := by
    have e : ∀ x y, (f x - f y) ^ 2 = f x ^ 2 - 2 * f x * f y + f y ^ 2 := by
      intro x y
      ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  rw [h1, h2]
  field_simp

/-- The double sum `∑_{p, q ∈ G} (a p + b q)(c p + e q)`. -/
theorem sum_sum_add_mul_add {ι : Type*} (G : Finset ι) (a b c e : ι → ℝ) :
    ∑ p ∈ G, ∑ q ∈ G, (a p + b q) * (c p + e q) =
      G.card * ∑ p ∈ G, a p * c p + (∑ p ∈ G, a p) * (∑ q ∈ G, e q) +
        (∑ q ∈ G, b q) * (∑ p ∈ G, c p) + G.card * ∑ q ∈ G, b q * e q := by
  have e1 : ∀ p q, (a p + b q) * (c p + e q) =
      a p * c p + a p * e q + b q * c p + b q * e q := by
    intro p q
    ring
  simp only [e1, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum,
    ← Finset.sum_mul]

/-- The variation of `F` along the row of height `k` of the grid `{0, …, L-1}²`. -/
noncomputable def gridRowVar (F : ℕ × ℕ → ℝ) (L k : ℕ) : ℝ :=
  ∑ a ∈ range (L - 1), |F (a + 1, k) - F (a, k)|

/-- The variation of `F` along the column of abscissa `a` of the grid `{0, …, L-1}²`. -/
noncomputable def gridColVar (F : ℕ × ℕ → ℝ) (L a : ℕ) : ℝ :=
  ∑ b ∈ range (L - 1), |F (a, b + 1) - F (a, b)|

theorem gridRowVar_nonneg (F : ℕ × ℕ → ℝ) (L k : ℕ) : 0 ≤ gridRowVar F L k :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem gridColVar_nonneg (F : ℕ × ℕ → ℝ) (L a : ℕ) : 0 ≤ gridColVar F L a :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- **The planar grid Sobolev inequality.** For `F` on `{0, …, L-1}²`,
`∑_p (F p - (F))² ≤ (1/2) (∑_k rowVar k + ∑_a colVar a)²`. -/
theorem sum_sq_sub_mean_le_grid (L : ℕ) (hL : 0 < L) (F : ℕ × ℕ → ℝ) :
    ∑ p ∈ range L ×ˢ range L,
        (F p - (∑ q ∈ range L ×ˢ range L, F q) / (range L ×ˢ range L).card) ^ 2 ≤
      (1 / 2) * (∑ k ∈ range L, gridRowVar F L k + ∑ a ∈ range L, gridColVar F L a) ^ 2 := by
  have hGne : (range L ×ˢ range L).Nonempty := ⟨(0, 0), by simp [hL]⟩
  have hGcard : ((range L ×ˢ range L).card : ℝ) = (L : ℝ) ^ 2 := by
    rw [Finset.card_product, Finset.card_range]
    push_cast
    ring
  have hsq : ∀ p ∈ range L ×ˢ range L, ∀ q ∈ range L ×ˢ range L,
      (F p - F q) ^ 2 ≤ (gridRowVar F L p.2 + gridColVar F L q.1) *
        (gridColVar F L p.1 + gridRowVar F L q.2) := by
    rintro ⟨p1, p2⟩ hp ⟨q1, q2⟩ hq
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp hq
    have h1 : |F (p1, p2) - F (q1, q2)| ≤ gridRowVar F L p2 + gridColVar F L q1 := by
      have ha := abs_sub_le_sum_range_abs_sub (fun a => F (a, p2)) hp.1 hq.1
      have hb := abs_sub_le_sum_range_abs_sub (fun b => F (q1, b)) hp.2 hq.2
      calc |F (p1, p2) - F (q1, q2)|
          = |(F (p1, p2) - F (q1, p2)) + (F (q1, p2) - F (q1, q2))| := by congr 1; ring
        _ ≤ |F (p1, p2) - F (q1, p2)| + |F (q1, p2) - F (q1, q2)| := abs_add_le _ _
        _ ≤ gridRowVar F L p2 + gridColVar F L q1 := add_le_add ha hb
    have h2 : |F (p1, p2) - F (q1, q2)| ≤ gridColVar F L p1 + gridRowVar F L q2 := by
      have ha := abs_sub_le_sum_range_abs_sub (fun b => F (p1, b)) hp.2 hq.2
      have hb := abs_sub_le_sum_range_abs_sub (fun a => F (a, q2)) hp.1 hq.1
      calc |F (p1, p2) - F (q1, q2)|
          = |(F (p1, p2) - F (p1, q2)) + (F (p1, q2) - F (q1, q2))| := by congr 1; ring
        _ ≤ |F (p1, p2) - F (p1, q2)| + |F (p1, q2) - F (q1, q2)| := abs_add_le _ _
        _ ≤ gridColVar F L p1 + gridRowVar F L q2 := add_le_add ha hb
    rw [← sq_abs, sq]
    exact mul_le_mul h1 h2 (abs_nonneg _)
      (add_nonneg (gridRowVar_nonneg _ _ _) (gridColVar_nonneg _ _ _))
  have hsum2 : ∀ φ : ℕ → ℝ, ∑ p ∈ range L ×ˢ range L, φ p.2 = L * ∑ k ∈ range L, φ k := by
    intro φ
    rw [Finset.sum_product]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hsum1 : ∀ φ : ℕ → ℝ, ∑ p ∈ range L ×ˢ range L, φ p.1 = L * ∑ k ∈ range L, φ k := by
    intro φ
    rw [Finset.sum_product]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum]
  have hsum12 : ∀ φ ψ : ℕ → ℝ, ∑ p ∈ range L ×ˢ range L, φ p.2 * ψ p.1 =
      (∑ k ∈ range L, φ k) * ∑ k ∈ range L, ψ k := by
    intro φ ψ
    rw [Finset.sum_product, Finset.sum_mul_sum, Finset.sum_comm]
  have hsum21 : ∀ φ ψ : ℕ → ℝ, ∑ p ∈ range L ×ˢ range L, ψ p.1 * φ p.2 =
      (∑ k ∈ range L, φ k) * ∑ k ∈ range L, ψ k := by
    intro φ ψ
    rw [← hsum12 φ ψ]
    exact Finset.sum_congr rfl fun p _ => mul_comm _ _
  have hdouble : ∑ p ∈ range L ×ˢ range L, ∑ q ∈ range L ×ˢ range L, (F p - F q) ^ 2 ≤
      (L : ℝ) ^ 2 * (∑ k ∈ range L, gridRowVar F L k + ∑ a ∈ range L, gridColVar F L a) ^ 2 := by
    calc ∑ p ∈ range L ×ˢ range L, ∑ q ∈ range L ×ˢ range L, (F p - F q) ^ 2
        ≤ ∑ p ∈ range L ×ˢ range L, ∑ q ∈ range L ×ˢ range L,
            (gridRowVar F L p.2 + gridColVar F L q.1) *
              (gridColVar F L p.1 + gridRowVar F L q.2) :=
          Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun q hq => hsq p hp q hq
      _ = _ := by
          rw [sum_sum_add_mul_add (range L ×ˢ range L) (fun p => gridRowVar F L p.2)
            (fun q => gridColVar F L q.1) (fun p => gridColVar F L p.1)
            (fun q => gridRowVar F L q.2)]
          rw [hsum12 (gridRowVar F L) (gridColVar F L), hsum21 (gridRowVar F L) (gridColVar F L),
            hsum2 (gridRowVar F L), hsum1 (gridColVar F L), hGcard]
          ring
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  rw [sum_sq_sub_mean_eq _ F hGne, hGcard, div_le_iff₀ (by positivity)]
  calc ∑ p ∈ range L ×ˢ range L, ∑ q ∈ range L ×ˢ range L, (F p - F q) ^ 2
      ≤ (L : ℝ) ^ 2 * (∑ k ∈ range L, gridRowVar F L k + ∑ a ∈ range L, gridColVar F L a) ^ 2 :=
        hdouble
    _ = _ := by ring

/-- For a locally finite graph and a vertex with at most `D` neighbours, the sum of the absolute
increments at the vertex is at most `√(2D)` times the magnitude of the gradient. -/
theorem sum_abs_adj_le_gradNormIn {d : ℕ} (G : SimpleGraph (Vertex d)) [G.LocallyFinite]
    (S : Finset (Vertex d)) (f : Vertex d → ℝ) (x : Vertex d) {D : ℕ} (hdeg : G.degree x ≤ D) :
    ∑ y ∈ S, (if G.Adj x y then |f x - f y| else 0) ≤ √(2 * D) * gradNormIn G S f x := by
  have hV : ∑ y ∈ S, (if G.Adj x y then |f x - f y| else 0) =
      ∑ y ∈ S.filter (G.Adj x), |f x - f y| := by
    rw [Finset.sum_filter]
  have hQ : (∑ y ∈ S, if G.Adj x y then (f x - f y) ^ 2 else 0) =
      ∑ y ∈ S.filter (G.Adj x), |f x - f y| ^ 2 := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun y _ => ?_
    split_ifs <;> simp [sq_abs]
  have hT : ((S.filter (G.Adj x)).card : ℝ) ≤ D := by
    have h1 : S.filter (G.Adj x) ⊆ G.neighborFinset x := fun y hy =>
      (SimpleGraph.mem_neighborFinset _ _ _).2 (Finset.mem_filter.1 hy).2
    exact_mod_cast ((Finset.card_le_card h1).trans
      ((SimpleGraph.card_neighborFinset_eq_degree _ _).le.trans hdeg))
  have hQ0 : 0 ≤ ∑ y ∈ S.filter (G.Adj x), |f x - f y| ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hg : gradNormIn G S f x ^ 2 = (1 / 2) * ∑ y ∈ S.filter (G.Adj x), |f x - f y| ^ 2 := by
    rw [gradNormIn, hQ, Real.sq_sqrt (by positivity)]
  have hcs := sq_sum_le_card_mul_sum_sq (s := S.filter (G.Adj x)) (f := fun y => |f x - f y|)
  have hnn : 0 ≤ ∑ y ∈ S.filter (G.Adj x), |f x - f y| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hrhs : 0 ≤ √(2 * D) * gradNormIn G S f x :=
    mul_nonneg (Real.sqrt_nonneg _) (gradNormIn_nonneg _ _ _ _)
  rw [hV]
  refine (pow_le_pow_iff_left₀ hnn hrhs two_ne_zero).1 ?_
  have hD : (√(2 * (D : ℝ))) ^ 2 = 2 * D := Real.sq_sqrt (by positivity)
  calc (∑ y ∈ S.filter (G.Adj x), |f x - f y|) ^ 2
      ≤ ((S.filter (G.Adj x)).card : ℝ) * ∑ y ∈ S.filter (G.Adj x), |f x - f y| ^ 2 := hcs
    _ ≤ (D : ℝ) * ∑ y ∈ S.filter (G.Adj x), |f x - f y| ^ 2 := mul_le_mul_of_nonneg_right hT hQ0
    _ = (√(2 * (D : ℝ)) * gradNormIn G S f x) ^ 2 := by
        rw [mul_pow, hD, hg]
        ring

/-- The vertex of a lattice square at offsets `p` from its corner. -/
def IntegerCube.gridPoint (B : IntegerCube 2) (p : ℕ × ℕ) : Vertex 2 :=
  ![B.corner 0 + p.1, B.corner 1 + p.2]

theorem IntegerCube.gridPoint_apply_zero (B : IntegerCube 2) (p : ℕ × ℕ) :
    B.gridPoint p 0 = B.corner 0 + p.1 := rfl

theorem IntegerCube.gridPoint_apply_one (B : IntegerCube 2) (p : ℕ × ℕ) :
    B.gridPoint p 1 = B.corner 1 + p.2 := rfl

theorem IntegerCube.mem_vertices_two {B : IntegerCube 2} {x : Vertex 2} :
    x ∈ B.vertices ↔ (B.corner 0 ≤ x 0 ∧ x 0 < B.corner 0 + B.size) ∧
      (B.corner 1 ≤ x 1 ∧ x 1 < B.corner 1 + B.size) := by
  rw [IntegerCube.mem_vertices]
  exact ⟨fun h => ⟨h 0, h 1⟩, fun h i => by fin_cases i; exacts [h.1, h.2]⟩

theorem IntegerCube.gridPoint_mem {B : IntegerCube 2} {p : ℕ × ℕ}
    (hp : p ∈ range B.size ×ˢ range B.size) : B.gridPoint p ∈ B.vertices := by
  rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
  rw [IntegerCube.mem_vertices_two, B.gridPoint_apply_zero, B.gridPoint_apply_one]
  omega

/-- Sums over a lattice square are sums over the grid of offsets. -/
theorem IntegerCube.sum_vertices_eq_sum_grid (B : IntegerCube 2) (g : Vertex 2 → ℝ) :
    ∑ x ∈ B.vertices, g x = ∑ p ∈ range B.size ×ˢ range B.size, g (B.gridPoint p) := by
  have hleft : ∀ x ∈ B.vertices,
      B.gridPoint ((x 0 - B.corner 0).toNat, (x 1 - B.corner 1).toNat) = x := by
    intro x hx
    rw [IntegerCube.mem_vertices_two] at hx
    funext i
    fin_cases i
    · show B.corner 0 + ((x 0 - B.corner 0).toNat : ℤ) = x 0
      omega
    · show B.corner 1 + ((x 1 - B.corner 1).toNat : ℤ) = x 1
      omega
  refine Finset.sum_nbij' (fun x => ((x 0 - B.corner 0).toNat, (x 1 - B.corner 1).toNat))
    B.gridPoint ?_ ?_ hleft ?_ ?_
  · intro x hx
    rw [IntegerCube.mem_vertices_two] at hx
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
    omega
  · intro p hp
    exact IntegerCube.gridPoint_mem hp
  · intro p _
    simp only [B.gridPoint_apply_zero, B.gridPoint_apply_one, add_sub_cancel_left,
      Int.toNat_natCast]
  · intro x hx
    rw [hleft x hx]

theorem IntegerCube.gridPoint_add_unit_zero (B : IntegerCube 2) (p : ℕ × ℕ) :
    B.gridPoint p + LatticeProb.unit (0 : Fin 2) = B.gridPoint (p.1 + 1, p.2) := by
  funext i
  fin_cases i
  · show B.corner 0 + (p.1 : ℤ) + 1 = B.corner 0 + ((p.1 + 1 : ℕ) : ℤ)
    push_cast
    ring
  · show B.corner 1 + (p.2 : ℤ) + 0 = B.corner 1 + (p.2 : ℤ)
    ring

theorem IntegerCube.gridPoint_add_unit_one (B : IntegerCube 2) (p : ℕ × ℕ) :
    B.gridPoint p + LatticeProb.unit (1 : Fin 2) = B.gridPoint (p.1, p.2 + 1) := by
  funext i
  fin_cases i
  · show B.corner 0 + (p.1 : ℤ) + 0 = B.corner 0 + (p.1 : ℤ)
    ring
  · show B.corner 1 + (p.2 : ℤ) + 1 = B.corner 1 + ((p.2 + 1 : ℕ) : ℤ)
    push_cast
    ring

private theorem sum_range_ite_succ_lt (L : ℕ) (h : ℕ → ℝ) :
    ∑ a ∈ range L, (if a + 1 < L then h a else 0) = ∑ a ∈ range (L - 1), h a := by
  rw [← Finset.sum_filter]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- **The planar lattice Sobolev inequality on a square**: for every function `f` on a lattice
square `B`, `∑_{x ∈ B} (f x - (f)_B)² ≤ 4 (∑_{x ∈ B} |∇f|(x))²`, with `|∇f|(x)` the magnitude of
the lattice gradient on `B`. -/
theorem IntegerCube.latticeSobolevOn_two (B : IntegerCube 2) (hB : 0 < B.size) :
    LatticeSobolevOn B.vertices 2 1 4 := by
  intro f
  have hcard : (B.vertices.card : ℝ) = ((range B.size ×ˢ range B.size).card : ℝ) := by
    rw [IntegerCube.card_vertices_eq, Finset.card_product, Finset.card_range]
    push_cast
    ring
  have hmean : (∑ y ∈ B.vertices, f y) / B.vertices.card =
      (∑ q ∈ range B.size ×ˢ range B.size, f (B.gridPoint q)) /
        (range B.size ×ˢ range B.size).card := by
    rw [B.sum_vertices_eq_sum_grid f, hcard]
  have hvar : ∑ x ∈ B.vertices, |f x - (∑ y ∈ B.vertices, f y) / B.vertices.card| ^ (2 : ℝ) =
      ∑ p ∈ range B.size ×ˢ range B.size, (f (B.gridPoint p) -
        (∑ q ∈ range B.size ×ˢ range B.size, f (B.gridPoint q)) /
          (range B.size ×ˢ range B.size).card) ^ 2 := by
    rw [hmean, B.sum_vertices_eq_sum_grid]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Real.rpow_two, sq_abs]
  -- the two forward increments at a vertex
  have hE : ∀ x : Vertex 2,
      ((if x + LatticeProb.unit (0 : Fin 2) ∈ B.vertices then
          |f x - f (x + LatticeProb.unit (0 : Fin 2))| else 0) +
        (if x + LatticeProb.unit (1 : Fin 2) ∈ B.vertices then
          |f x - f (x + LatticeProb.unit (1 : Fin 2))| else 0)) ≤
      ∑ y ∈ B.vertices, (if (nearestNeighborGraph 2).Adj x y then |f x - f y| else 0) := by
    intro x
    have hne : x + LatticeProb.unit (0 : Fin 2) ≠ x + LatticeProb.unit (1 : Fin 2) := by
      intro h
      have := congrFun h 0
      simp [LatticeProb.unit] at this
    have hadj0 : (nearestNeighborGraph 2).Adj x (x + LatticeProb.unit (0 : Fin 2)) :=
      ⟨0, Or.inl rfl⟩
    have hadj1 : (nearestNeighborGraph 2).Adj x (x + LatticeProb.unit (1 : Fin 2)) :=
      ⟨1, Or.inl rfl⟩
    calc ((if x + LatticeProb.unit (0 : Fin 2) ∈ B.vertices then
            |f x - f (x + LatticeProb.unit (0 : Fin 2))| else 0) +
          (if x + LatticeProb.unit (1 : Fin 2) ∈ B.vertices then
            |f x - f (x + LatticeProb.unit (1 : Fin 2))| else 0))
        = ∑ y ∈ ({x + LatticeProb.unit (0 : Fin 2), x + LatticeProb.unit (1 : Fin 2)} :
            Finset (Vertex 2)), (if y ∈ B.vertices then
              (if (nearestNeighborGraph 2).Adj x y then |f x - f y| else 0) else 0) := by
          rw [Finset.sum_pair hne, if_pos hadj0, if_pos hadj1]
      _ = ∑ y ∈ ({x + LatticeProb.unit (0 : Fin 2), x + LatticeProb.unit (1 : Fin 2)} :
            Finset (Vertex 2)).filter (· ∈ B.vertices),
              (if (nearestNeighborGraph 2).Adj x y then |f x - f y| else 0) :=
          (Finset.sum_filter _ _).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (fun y hy => (Finset.mem_filter.1 hy).2)
          fun _ _ _ => by split_ifs <;> positivity
  -- the row and column variations are the sums of the forward increments
  have hgrid : ∑ k ∈ range B.size, gridRowVar (fun p => f (B.gridPoint p)) B.size k +
      ∑ a ∈ range B.size, gridColVar (fun p => f (B.gridPoint p)) B.size a =
      ∑ p ∈ range B.size ×ˢ range B.size,
        ((if B.gridPoint p + LatticeProb.unit (0 : Fin 2) ∈ B.vertices then
            |f (B.gridPoint p) - f (B.gridPoint p + LatticeProb.unit (0 : Fin 2))| else 0) +
          (if B.gridPoint p + LatticeProb.unit (1 : Fin 2) ∈ B.vertices then
            |f (B.gridPoint p) - f (B.gridPoint p + LatticeProb.unit (1 : Fin 2))| else 0)) := by
    have hmem0 : ∀ p ∈ range B.size ×ˢ range B.size,
        (B.gridPoint p + LatticeProb.unit (0 : Fin 2) ∈ B.vertices ↔ p.1 + 1 < B.size) := by
      intro p hp
      rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
      rw [B.gridPoint_add_unit_zero, IntegerCube.mem_vertices_two, B.gridPoint_apply_zero,
        B.gridPoint_apply_one]
      push_cast
      omega
    have hmem1 : ∀ p ∈ range B.size ×ˢ range B.size,
        (B.gridPoint p + LatticeProb.unit (1 : Fin 2) ∈ B.vertices ↔ p.2 + 1 < B.size) := by
      intro p hp
      rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
      rw [B.gridPoint_add_unit_one, IntegerCube.mem_vertices_two, B.gridPoint_apply_zero,
        B.gridPoint_apply_one]
      push_cast
      omega
    have hterm : ∀ p ∈ range B.size ×ˢ range B.size,
        ((if B.gridPoint p + LatticeProb.unit (0 : Fin 2) ∈ B.vertices then
            |f (B.gridPoint p) - f (B.gridPoint p + LatticeProb.unit (0 : Fin 2))| else 0) +
          (if B.gridPoint p + LatticeProb.unit (1 : Fin 2) ∈ B.vertices then
            |f (B.gridPoint p) - f (B.gridPoint p + LatticeProb.unit (1 : Fin 2))| else 0)) =
        (if p.1 + 1 < B.size then
            |f (B.gridPoint (p.1 + 1, p.2)) - f (B.gridPoint p)| else 0) +
          (if p.2 + 1 < B.size then
            |f (B.gridPoint (p.1, p.2 + 1)) - f (B.gridPoint p)| else 0) := by
      intro p hp
      rw [if_congr (hmem0 p hp) rfl rfl, if_congr (hmem1 p hp) rfl rfl,
        B.gridPoint_add_unit_zero, B.gridPoint_add_unit_one, abs_sub_comm (f (B.gridPoint p)),
        abs_sub_comm (f (B.gridPoint p))]
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_product,
      Finset.sum_product, Finset.sum_comm]
    dsimp only
    congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [sum_range_ite_succ_lt B.size (fun a => |f (B.gridPoint (a + 1, k)) -
        f (B.gridPoint (a, k))|)]
      rfl
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [sum_range_ite_succ_lt B.size (fun b => |f (B.gridPoint (a, b + 1)) -
        f (B.gridPoint (a, b))|)]
      rfl
  have hgrad : ∑ k ∈ range B.size, gridRowVar (fun p => f (B.gridPoint p)) B.size k +
      ∑ a ∈ range B.size, gridColVar (fun p => f (B.gridPoint p)) B.size a ≤
      √(2 * ((2 * 2 : ℕ) : ℝ)) *
        ∑ x ∈ B.vertices, gradNormIn (nearestNeighborGraph 2) B.vertices f x := by
    rw [hgrid, ← B.sum_vertices_eq_sum_grid (fun x =>
      (if x + LatticeProb.unit (0 : Fin 2) ∈ B.vertices then
          |f x - f (x + LatticeProb.unit (0 : Fin 2))| else 0) +
        (if x + LatticeProb.unit (1 : Fin 2) ∈ B.vertices then
          |f x - f (x + LatticeProb.unit (1 : Fin 2))| else 0)), Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => (hE x).trans ?_
    exact sum_abs_adj_le_gradNormIn _ _ _ _ (LatticeProb.Graph.Zd.degree_eq x).le
  have hX0 : 0 ≤ ∑ k ∈ range B.size, gridRowVar (fun p => f (B.gridPoint p)) B.size k +
      ∑ a ∈ range B.size, gridColVar (fun p => f (B.gridPoint p)) B.size a :=
    add_nonneg (Finset.sum_nonneg fun _ _ => gridRowVar_nonneg _ _ _)
      (Finset.sum_nonneg fun _ _ => gridColVar_nonneg _ _ _)
  have hY0 : 0 ≤ ∑ x ∈ B.vertices, gradNormIn (nearestNeighborGraph 2) B.vertices f x :=
    Finset.sum_nonneg fun _ _ => gradNormIn_nonneg _ _ _ _
  rw [hvar]
  simp only [Real.rpow_one, div_one, Real.rpow_two]
  refine (sum_sq_sub_mean_le_grid B.size hB (fun p => f (B.gridPoint p))).trans ?_
  have h8 : (√(2 * ((2 * 2 : ℕ) : ℝ))) ^ 2 = 8 := by
    rw [Real.sq_sqrt (by positivity)]
    norm_num
  calc (1 / 2) * (∑ k ∈ range B.size, gridRowVar (fun p => f (B.gridPoint p)) B.size k +
        ∑ a ∈ range B.size, gridColVar (fun p => f (B.gridPoint p)) B.size a) ^ 2
      ≤ (1 / 2) * (√(2 * ((2 * 2 : ℕ) : ℝ)) *
          ∑ x ∈ B.vertices, gradNormIn (nearestNeighborGraph 2) B.vertices f x) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hX0 hgrad 2) (by norm_num)
    _ = 4 * (∑ x ∈ B.vertices, gradNormIn (nearestNeighborGraph 2) B.vertices f x) ^ 2 := by
        rw [mul_pow, h8]
        ring

end Rigidity.Percolation
