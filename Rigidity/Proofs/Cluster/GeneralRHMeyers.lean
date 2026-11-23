import Rigidity.Proofs.Cluster.GeneralRHLocal

/-!
# The Meyers estimate above a partition of local reverse Hölder cubes, in every dimension

Step 1 of the proof of Proposition 3.8 of Armstrong and Dario uses the reverse Hölder inequality on
the predecessors of the cells of the partition `𝓡` for the gradients of a solution on a larger
cluster. With the local family `rhGood A₀` of `GeneralRHLocal` this holds for any finite set `U₀`
of `ℤ^d` closed under the open edges inside `3□` and any function `u` harmonic at the points of
`U₀ ∩ 3□` all of whose open edges stay in `U₀` (in the application `U₀` is the crossing cluster
`𝒞_*(V)` of a resolved cube `V ⊇ 3□`). For a child `cube k z` of a predecessor, the set
`U₀ ∩ 3 cube k z` is closed under the open edges inside the triple and `u` is harmonic on it; the
energy densities agree on the child and are smaller on the triple
(`avg_clusterEnergy_le_of_rhCube`). Averaging over the `3^d` children gives the reverse Hölder
inequality on the predecessor with constant `3^{d+1} max(1, A₀)` (`avg_clusterEnergy_le_of_rhGood`),
and `meyers_triadic_uniform` gives the Meyers estimate with `ε` and `t` depending only on `d` and
`A₀` (`meyers_rh_uniform`). The planar case is `PlanarRHMeyers`.
-/

namespace Rigidity.Proofs.Cluster.GeneralDim

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation Rigidity.External
open scoped BigOperators Classical ENNReal

variable {d : ℕ} {ω : Configuration d}

/-- A lattice neighbour of a point of a cube lies in its triple. -/
theorem mem_enl_of_near_cube {k : ℕ} {z a b : Vertex d} (ha : a ∈ cube k z)
    (hb : ∀ i, |b i - a i| ≤ 1) : b ∈ enl 1 k z := by
  rw [cube, mem_box] at ha
  rw [enl, mem_box]
  intro i
  have h1 := ha i
  have h2 := hb i
  have h3 : halfSide (k + 1) = 3 * halfSide k + 1 := rfl
  have h4 := halfSide_nonneg k
  calc |b i - center k z i| ≤ |b i - a i| + |a i - center k z i| := abs_sub_le _ _ _
    _ ≤ 1 + halfSide k := add_le_add h2 h1
    _ ≤ halfSide (k + 1) := by rw [h3]; linarith

/-- **The reverse Hölder inequality on a cube for the energy of a set closed under its open
edges.** -/
theorem avg_clusterEnergy_le_of_rhCube {U₀ : Finset (Vertex d)} {u : Vertex d → ℝ} {A₀ : ℝ}
    (hA₀ : 0 ≤ A₀) {k : ℕ} {z : Vertex d}
    (hcl : ∀ a ∈ U₀, ∀ b, (openGraph ω).Adj a b → b ∈ enl 1 k z → b ∈ U₀)
    (hu : ∀ a ∈ U₀, a ∈ enl 1 k z → (∀ b, (openGraph ω).Adj a b → b ∈ U₀) →
      openLaplacian ω u a = 0)
    (hRH : RHCube A₀ ω k z) :
    avg (cube k z) (clusterEnergy ω U₀ u) ≤
      A₀ * avg (enl 1 k z) (fun x => clusterEnergy ω U₀ u x ^ ((d : ℝ) / (d + 1))) ^
        (((d : ℝ) + 1) / d) := by
  set C := U₀.filter (· ∈ enl 1 k z) with hC
  have hCsub : C ⊆ enl 1 k z := fun a ha => (Finset.mem_filter.1 ha).2
  have hCU : C ⊆ U₀ := Finset.filter_subset _ _
  have hclC : ∀ a ∈ C, ∀ b, (openGraph ω).Adj a b → b ∈ enl 1 k z → b ∈ C := fun a ha b hadj hb =>
    Finset.mem_filter.2 ⟨hcl a (hCU ha) b hadj hb, hb⟩
  have huC : ∀ a ∈ C, (∀ b, (openGraph ω).Adj a b → b ∈ C) → openLaplacian ω u a = 0 :=
    fun a ha hall => hu a (hCU ha) (hCsub ha) fun b hb => hCU (hall b hb)
  have h1 := hRH C hCsub hclC u huC
  have heq : ∀ a ∈ cube k z, clusterEnergy ω U₀ u a = clusterEnergy ω C u a := by
    intro a ha
    have haE := cube_subset_enl 1 k z ha
    unfold clusterEnergy
    by_cases haU : a ∈ U₀
    · have haC : a ∈ C := Finset.mem_filter.2 ⟨haU, haE⟩
      rw [if_pos haU, if_pos haC]
      unfold clusterGradSq
      congr 2
      refine Finset.filter_congr fun b hb => ?_
      have hadj := (SimpleGraph.mem_neighborFinset _ _ _).1 hb
      have hbE : b ∈ enl 1 k z := mem_enl_of_near_cube ha fun i => by
        rw [abs_sub_comm]; exact abs_sub_le_one_of_openGraph_adj hadj i
      constructor
      · intro hbU; exact Finset.mem_filter.2 ⟨hbU, hbE⟩
      · intro hbC; exact hCU hbC
    · have haC : a ∉ C := fun h => haU (hCU h)
      rw [if_neg haU, if_neg haC]
  have hle : ∀ a, clusterEnergy ω C u a ≤ clusterEnergy ω U₀ u a := by
    intro a
    unfold clusterEnergy
    by_cases haC : a ∈ C
    · rw [if_pos haC, if_pos (hCU haC)]
      exact clusterGradSq_le_of_subset ω hCU u a
    · rw [if_neg haC]
      split_ifs
      · exact clusterGradSq_nonneg ω U₀ u a
      · exact le_rfl
  have e1 : avg (cube k z) (clusterEnergy ω U₀ u) = avg (cube k z) (clusterEnergy ω C u) := by
    unfold avg
    rw [Finset.sum_congr rfl heq]
  rw [e1]
  refine h1.trans ?_
  have hθ : (0 : ℝ) ≤ (d : ℝ) / (d + 1) := by positivity
  refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ?_ ?_ (by positivity)) hA₀
  · exact div_nonneg (Finset.sum_nonneg fun a _ =>
      Real.rpow_nonneg (clusterEnergy_nonneg ω C u a) _) (Nat.cast_nonneg _)
  · unfold avg
    refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun a _ => ?_) (Nat.cast_nonneg _)
    exact Real.rpow_le_rpow (clusterEnergy_nonneg ω C u a) (hle a) hθ

theorem three_pow_rpow_succ_div (hd : 1 ≤ d) :
    ((3 : ℝ) ^ d) ^ (((d : ℝ) + 1) / d) = 3 ^ (d + 1) := by
  have hd0 : (d : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  rw [← Real.rpow_natCast (3 : ℝ) d, ← Real.rpow_mul (by norm_num),
    show (d : ℝ) * (((d : ℝ) + 1) / d) = ((d + 1 : ℕ) : ℝ) by push_cast; field_simp,
    Real.rpow_natCast]

theorem rpow_div_three_pow (hd : 1 ≤ d) (a : ℝ) (ha : 0 ≤ a) :
    (a ^ ((d : ℝ) / (d + 1)) / (3 : ℝ) ^ d) ^ (((d : ℝ) + 1) / d) = a / 3 ^ (d + 1) := by
  have hd0 : (d : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  rw [Real.div_rpow (Real.rpow_nonneg ha _) (by positivity), ← Real.rpow_mul ha,
    three_pow_rpow_succ_div hd,
    show (d : ℝ) / (d + 1) * (((d : ℝ) + 1) / d) = 1 by field_simp, Real.rpow_one]

/-- **The reverse Hölder inequality on a predecessor** from the local family, with constant
`3^{d+1} max(1, A₀)`. -/
theorem avg_clusterEnergy_le_of_rhGood (hd : 1 ≤ d) {U₀ : Finset (Vertex d)} {u : Vertex d → ℝ}
    {A₀ : ℝ} {k : ℕ} {y : Vertex d}
    (hcl : ∀ a ∈ U₀, ∀ b, (openGraph ω).Adj a b → b ∈ enl 1 k y → b ∈ U₀)
    (hu : ∀ a ∈ U₀, a ∈ enl 1 k y → (∀ b, (openGraph ω).Adj a b → b ∈ U₀) →
      openLaplacian ω u a = 0)
    (hgood : (⟨k, idx k y⟩ : TriadicCube d) ∈ rhGood A₀ ω) :
    avg (cube k y) (clusterEnergy ω U₀ u) ≤
      3 ^ (d + 1) * max 1 A₀ * avg (enl 1 k y) (fun x => clusterEnergy ω U₀ u x ^
        ((d : ℝ) / (d + 1))) ^ (((d : ℝ) + 1) / d) := by
  set G := clusterEnergy ω U₀ u with hGdef
  have hG0 : ∀ x, 0 ≤ G x := fun x => clusterEnergy_nonneg _ _ _ x
  set θ : ℝ := (d : ℝ) / (d + 1) with hθ
  set ι : ℝ := ((d : ℝ) + 1) / d with hι
  have hθ0 : 0 ≤ θ := by rw [hθ]; positivity
  have hι0 : 0 ≤ ι := by rw [hι]; positivity
  have hM1 : (1 : ℝ) ≤ max 1 A₀ := le_max_left _ _
  have hD : (1 : ℝ) ≤ 3 ^ (d + 1) := one_le_pow₀ (by norm_num)
  have havg0 : 0 ≤ avg (enl 1 k y) (fun x => G x ^ θ) :=
    div_nonneg (Finset.sum_nonneg fun x _ => Real.rpow_nonneg (hG0 x) _) (Nat.cast_nonneg _)
  cases k with
  | zero =>
    rw [avg, cube_zero, Finset.sum_singleton, Finset.card_singleton, Nat.cast_one, div_one]
    have hyE : y ∈ enl 1 0 y := cube_subset_enl 1 0 y (mem_cube_self 0 y)
    have hcard : ((enl 1 0 y).card : ℝ) = 3 ^ d := by rw [card_enl]; norm_num
    have hlow : G y ^ θ / 3 ^ d ≤ avg (enl 1 0 y) (fun x => G x ^ θ) := by
      rw [avg, hcard]
      exact div_le_div_of_nonneg_right (Finset.single_le_sum
        (f := fun x => G x ^ θ) (fun x _ => Real.rpow_nonneg (hG0 x) _) hyE) (by positivity)
    have h1 : G y / 3 ^ (d + 1) ≤ avg (enl 1 0 y) (fun x => G x ^ θ) ^ ι := by
      rw [← rpow_div_three_pow hd (G y) (hG0 y)]
      exact Real.rpow_le_rpow (div_nonneg (Real.rpow_nonneg (hG0 y) _) (by positivity)) hlow hι0
    have h2 : (0 : ℝ) ≤ avg (enl 1 0 y) (fun x => G x ^ θ) ^ ι := Real.rpow_nonneg havg0 _
    have h3 := mul_le_mul_of_nonneg_right hM1 h2
    rw [one_mul] at h3
    have h4 := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ 3 ^ (d + 1) by positivity)
    have h5 := mul_le_mul_of_nonneg_left h3 (show (0 : ℝ) ≤ 3 ^ (d + 1) by positivity)
    have h6 : (3 : ℝ) ^ (d + 1) * (G y / 3 ^ (d + 1)) = G y := by field_simp
    calc G y = 3 ^ (d + 1) * (G y / 3 ^ (d + 1)) := h6.symm
      _ ≤ _ := h4
      _ ≤ _ := h5
      _ = _ := by ring
  | succ k' =>
    have hsub : ∀ z ∈ cube (k' + 1) y, cube k' z ⊆ cube (k' + 1) y := fun z hz =>
      (cube_subset_succ k' z).trans (cube_eq_of_mem hz).le
    have henl : ∀ z ∈ cube (k' + 1) y, enl 1 k' z ⊆ enl 1 (k' + 1) y := fun z hz =>
      (enl_subset_enl (Nat.le_succ k') 1 z).trans (enl_eq_of_mem hz).le
    have hchild : ∀ z ∈ cube (k' + 1) y, avg (cube k' z) G ≤
        3 ^ (d + 1) * max 1 A₀ * avg (enl 1 (k' + 1) y) (fun x => G x ^ θ) ^ ι := by
      intro z hz
      have hRH : RHCube (max 1 A₀) ω k' z := by
        have h := hgood k' rfl z (mem_triadicCube_idx_iff.2 hz)
        intro C hC hclC v hv
        refine (h C hC hclC v hv).trans ?_
        refine mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg ?_ _)
        exact div_nonneg (Finset.sum_nonneg fun x _ =>
          Real.rpow_nonneg (clusterEnergy_nonneg _ _ _ x) _) (Nat.cast_nonneg _)
      have h1 := avg_clusterEnergy_le_of_rhCube (by positivity)
        (fun a ha b hadj hb => hcl a ha b hadj (henl z hz hb))
        (fun a ha haE hall => hu a ha (henl z hz haE) hall) hRH
      refine h1.trans ?_
      have hcard : ((enl 1 (k' + 1) y).card : ℝ) = 3 ^ d * (enl 1 k' z).card := by
        rw [card_enl, card_enl, ← mul_pow]
        ring
      have hpos : (0 : ℝ) < (enl 1 k' z).card := by rw [card_enl]; positivity
      have hav : avg (enl 1 k' z) (fun x => G x ^ θ) ≤
          3 ^ d * avg (enl 1 (k' + 1) y) (fun x => G x ^ θ) := by
        rw [avg, avg, hcard, div_le_iff₀ hpos]
        have : ∑ x ∈ enl 1 k' z, G x ^ θ ≤ ∑ x ∈ enl 1 (k' + 1) y, G x ^ θ :=
          Finset.sum_le_sum_of_subset_of_nonneg (henl z hz)
            fun x _ _ => Real.rpow_nonneg (hG0 x) _
        have e : 3 ^ d * ((∑ x ∈ enl 1 (k' + 1) y, G x ^ θ) / (3 ^ d * (enl 1 k' z).card)) *
            (enl 1 k' z).card = ∑ x ∈ enl 1 (k' + 1) y, G x ^ θ := by
          field_simp
        rw [e]
        exact this
      have h9 : ((3 : ℝ) ^ d * avg (enl 1 (k' + 1) y) (fun x => G x ^ θ)) ^ ι =
          3 ^ (d + 1) * avg (enl 1 (k' + 1) y) (fun x => G x ^ θ) ^ ι := by
        rw [Real.mul_rpow (by positivity) havg0, hι, three_pow_rpow_succ_div hd]
      calc max 1 A₀ * avg (enl 1 k' z) (fun x => G x ^ θ) ^ ι
          ≤ max 1 A₀ * (3 ^ d * avg (enl 1 (k' + 1) y) (fun x => G x ^ θ)) ^ ι :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (div_nonneg (Finset.sum_nonneg
              fun x _ => Real.rpow_nonneg (hG0 x) _) (Nat.cast_nonneg _)) hav hι0) (by positivity)
        _ = 3 ^ (d + 1) * max 1 A₀ * avg (enl 1 (k' + 1) y) (fun x => G x ^ θ) ^ ι := by
            rw [h9]; ring
    have hpos : (0 : ℝ) < (cube (k' + 1) y).card := card_cube_pos _ _
    rw [avg, sum_eq_sum_cube_avg hsub G, div_le_iff₀ hpos]
    calc ∑ z ∈ cube (k' + 1) y, (∑ x ∈ cube k' z, G x) / (cube k' z).card
        ≤ ∑ _z ∈ cube (k' + 1) y,
            3 ^ (d + 1) * max 1 A₀ * avg (enl 1 (k' + 1) y) (fun x => G x ^ θ) ^ ι :=
          Finset.sum_le_sum fun z hz => hchild z hz
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- **The Meyers estimate above a partition of local reverse Hölder cubes, with `ε` and `t` chosen
before the moment bound** (Armstrong and Dario, Proposition 3.8, deterministic part, in every
dimension, with the predecessors in the family of Definition 3.7): for a finite set `U₀` closed
under the open edges inside `3□ = enl 1 n x₀` and `u` harmonic at the points of `U₀ ∩ 3□` all of
whose open edges stay in `U₀`, if the cells `cube (s x) x` have comparable neighbours, tile `3□`,
their predecessors inside `3□` are in `rhGood A₀ ω` and `∑_{x ∈ □} (3^{s(x)})^t ≤ K |□|`, then
`avg_□ E^{1+ε/2} ≤ C (avg_{3□} E)^{1+ε/2}`, `E = |∇u 1_{𝐚≠0}|²` on `U₀`. -/
theorem meyers_rh_uniform (hd : 1 ≤ d) (A₀ : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ t : ℝ, 0 < t ∧ ∀ K : ℝ, 0 ≤ K → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ω : Configuration d) (U₀ : Finset (Vertex d)) (u : Vertex d → ℝ) (n : ℕ)
        (x₀ : Vertex d) (s : Vertex d → ℕ),
        (∀ a ∈ U₀, ∀ b, (openGraph ω).Adj a b → b ∈ enl 1 n x₀ → b ∈ U₀) →
        (∀ a ∈ U₀, a ∈ enl 1 n x₀ → (∀ b, (openGraph ω).Adj a b → b ∈ U₀) →
          openLaplacian ω u a = 0) →
        (∀ x, ∀ z ∈ cube (s x) x, s z = s x) →
        (∀ x y, supDist x y ≤ 1 → s y ≤ s x + 1) →
        (∀ z ∈ enl 1 n x₀, cube (s z) z ⊆ enl 1 n x₀) →
        (∀ k y, s y ≤ k → enl 1 k y ⊆ enl 1 n x₀ →
          (⟨k, idx k y⟩ : TriadicCube d) ∈ rhGood A₀ ω) →
        ∑ x ∈ cube n x₀, ((3 : ℝ) ^ s x) ^ t ≤ K * (cube n x₀).card →
        avg (cube n x₀) (fun x => clusterEnergy ω U₀ u x ^ (1 + ε / 2)) ≤
          C * avg (enl 1 n x₀) (clusterEnergy ω U₀ u) ^ (1 + ε / 2) := by
  have hA : (1 : ℝ) ≤ 3 ^ (d + 1) * max 1 A₀ :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (le_max_left _ _)
  obtain ⟨ε, hε, t, ht, hM⟩ := meyers_triadic_uniform hd hA
  refine ⟨ε, hε, t, ht, fun K hK => ?_⟩
  obtain ⟨C, hC, hMK⟩ := hM K hK
  refine ⟨C, hC, ?_⟩
  intro ω U₀ u n x₀ s hcl hu hcell hnb hΩ hcubes hmom
  refine hMK n x₀ _ s (fun x => clusterEnergy_nonneg _ _ _ x) hcell hnb hΩ
    (fun k y hk hsub => ?_) hmom
  exact avg_clusterEnergy_le_of_rhGood hd (fun a ha b hadj hb => hcl a ha b hadj (hsub hb))
    (fun a ha haE hall => hu a ha (hsub haE) hall) (hcubes k y hk hsub)

end Rigidity.Proofs.Cluster.GeneralDim
