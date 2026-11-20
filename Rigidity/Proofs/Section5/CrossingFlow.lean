import Rigidity.Proofs.Section5.LoopFromCrossings
import Rigidity.Proofs.Section5.WellConnectedLink
import Rigidity.Proofs.Section5.WalkFamilyFlow

/-!
# Unit flows along crossings of thin rectangles

Fix `L, w, k, N` and two vertices `y, x` of an infinite open cluster `C` of `ℤ²`. Suppose that

* each of the `k` disjoint rectangles `[-L, L] × [y₁ + i(w + 1), y₁ + i(w + 1) + w]` has an open
  horizontal crossing `h_i`, and each of the `k` disjoint rectangles
  `[x₀ + j(w + 1), x₀ + j(w + 1) + w] × [-L, L]` has an open vertical crossing `v_j`;
* the rectangle `[y₀, y₀ + w] × [y₁, y₁ + k(w + 1)]` has an open vertical crossing `a`, and the
  rectangle `[x₀, x₀ + k(w + 1)] × [x₁, x₁ + w]` has an open horizontal crossing `b`;
* the cubes of radius `N` centred at `y` and `x` are well-connected.

By the crossing lemma, `a` meets every `h_i`, every `h_i` meets every `v_j` and every `v_j`
meets `b`. The starting points of `a` and `b` are within distance `w` of `y` and `x` and start
long open paths, so they are linked to `y` and `x` inside the well-connected cubes. The walks
`y → a → h_i → v_j → b → x`, `i, j < k`, give a unit flow from `y` to `x` inside `C`, with
energy at most `crossFlowBound L w k N`, of order `N³ + k w² + L w / k`.
-/

open LatticeProb.Percolation LatticeProb.Network Rigidity.External Rigidity.Proofs.S3
open scoped Classical

namespace Rigidity.Proofs.Section5

variable {ω : Configuration 2}

/-- The lattice points of the rectangle `[a, a + m] × [b, b + n]`. -/
noncomputable def rectFinset (a b : ℤ) (m n : ℕ) : Finset (Vertex 2) :=
  ((Finset.Icc a (a + m)) ×ˢ (Finset.Icc b (b + n))).image fun z => ![z.1, z.2]

theorem mem_rectFinset {a b : ℤ} {m n : ℕ} {z : Vertex 2} :
    z ∈ rectFinset a b m n ↔ (a ≤ z 0 ∧ z 0 ≤ a + m) ∧ b ≤ z 1 ∧ z 1 ≤ b + n := by
  constructor
  · intro hz
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hz
    obtain ⟨h1, h2⟩ := Finset.mem_product.1 hq
    simpa using And.intro (Finset.mem_Icc.1 h1) (Finset.mem_Icc.1 h2)
  · rintro ⟨h1, h2⟩
    refine Finset.mem_image.2 ⟨(z 0, z 1), Finset.mem_product.2
      ⟨Finset.mem_Icc.2 h1, Finset.mem_Icc.2 h2⟩, ?_⟩
    funext i
    fin_cases i <;> rfl

theorem card_rectFinset_le (a b : ℤ) (m n : ℕ) :
    (rectFinset a b m n).card ≤ (m + 1) * (n + 1) := by
  refine Finset.card_image_le.trans ?_
  rw [Finset.card_product, Int.card_Icc, Int.card_Icc]
  apply le_of_eq
  congr 1 <;> omega

/-- In the graph induced by the open edges on a set of vertices, every degree is at most four. -/
theorem induce_openGraph_degree_le (V : Finset (Vertex 2)) (v : V) :
    ((openGraph ω).induce (V : Set (Vertex 2))).degree v ≤ 4 := by
  let G := openGraph ω
  let H := G.induce (V : Set (Vertex 2))
  let e : H.neighborSet v ↪ G.neighborSet v.val :=
    ⟨fun w => ⟨w.val.val, w.property⟩, fun w w' h => by
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : G.neighborSet v.val => z.val) h⟩
  calc
    H.degree v ≤ G.degree v.val := by
      rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
      exact Fintype.card_le_of_injective e e.injective
    _ ≤ 2 * 2 := openGraph_degree_le ω v.val

/-- Integer multiples of `c + 1` whose windows of length `c` share a point coincide. -/
theorem eq_of_window_overlap {a b c t : ℤ} (hc : 0 ≤ c)
    (ha : a * (c + 1) ≤ t ∧ t ≤ a * (c + 1) + c) (hb : b * (c + 1) ≤ t ∧ t ≤ b * (c + 1) + c) :
    a = b := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have : a + 1 ≤ b := h
    nlinarith
  · have : b + 1 ≤ a := h
    nlinarith

/-- An open walk inside a set starting at a point of the cube `z + Q_M` and ending outside the cube
`z + Q_M` makes its start a start of a long open path. -/
theorem startsLongPath_of_reachIn {S : Set (Vertex 2)} {u v : Vertex 2} {M : ℕ}
    (h : ReachIn ω S u v) (i : Fin 2) (hfar : u i + M < v i) : StartsLongPath ω u M := by
  obtain ⟨W, -⟩ := h
  refine ⟨v, W.bypass, W.bypass_isPath, ?_⟩
  have hcoord := abs_getVert_sub_le (openGraph_le ω) W.bypass W.bypass.length i
  rw [SimpleGraph.Walk.getVert_length, abs_le] at hcoord
  omega

/-- The energy bound of the flow along a crossing structure. -/
noncomputable def crossFlowBound (L w k N : ℕ) : ℝ :=
  4 * (2 * (((4 * N + 1) * (2 * wcSubRadius 2 N + 1) ^ 2 : ℕ) + 1 : ℝ) +
    2 * (((w + 1) * (k * (w + 1) + 1) : ℕ) : ℝ) + 8 * (2 * L + 1) * (w + 1) / k)

/-- A vertex of a walk from a vertex of a component lies in the component. -/
theorem mem_supp_of_mem_support {C : OpenComponent ω} {u v : Vertex 2} (hu : u ∈ C.supp)
    (W : (openGraph ω).Walk u v) {z : Vertex 2} (hz : z ∈ W.support) : z ∈ C.supp := by
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hu ⊢
  rw [← hu]
  exact (SimpleGraph.ConnectedComponent.sound (W.takeUntil z hz).reachable).symm

/-- **Flows along crossing structures.** Under the crossing and well-connectedness hypotheses
described in the module docstring, there is a unit flow from `y` to `x` on a finite set of
vertices of `C` whose energy is at most `crossFlowBound L w k N`. -/
theorem exists_flow_of_crossings (C : OpenComponent ω) (hC : C.supp.Infinite) (y x : C)
    {L w k N : ℕ} (hk : 0 < k) (hN : 1 ≤ N) (hwN : w ≤ N) (hNH : N < k * (w + 1))
    (hy0 : -(L : ℤ) ≤ y.val 0) (hy0' : y.val 0 + w ≤ L) (hy1 : -(L : ℤ) ≤ y.val 1)
    (hy1' : y.val 1 + k * (w + 1) ≤ L)
    (hx0 : -(L : ℤ) ≤ x.val 0) (hx0' : x.val 0 + k * (w + 1) ≤ L) (hx1 : -(L : ℤ) ≤ x.val 1)
    (hx1' : x.val 1 + w ≤ L)
    (hwcy : IsWellConnected ω y.val N) (hwcx : IsWellConnected ω x.val N)
    (hrow : ∀ i : Fin k,
      HasOpenCrossing ω ![-(L : ℤ), y.val 1 + (i : ℕ) * (w + 1)] (2 * L) w 0)
    (hcol : ∀ j : Fin k,
      HasOpenCrossing ω ![x.val 0 + (j : ℕ) * (w + 1), -(L : ℤ)] (2 * L) w 1)
    (ha : HasOpenCrossing ω ![y.val 0, y.val 1] (k * (w + 1)) w 1)
    (hb : HasOpenCrossing ω ![x.val 0, x.val 1] (k * (w + 1)) w 0) :
    ∃ V : Finset (Vertex 2), (∀ z ∈ V, z ∈ C.supp) ∧
      ∃ (hyV : y.val ∈ V) (hxV : x.val ∈ V) (θ : V → V → ℝ),
        IsFlow ((openGraph ω).induce (V : Set (Vertex 2))) θ ∧
        (∀ z : V, divergence ((openGraph ω).induce (V : Set (Vertex 2))) θ z =
          (if z = ⟨y.val, hyV⟩ then 1 else 0) - (if z = ⟨x.val, hxV⟩ then 1 else 0)) ∧
        flowEnergyOn ((openGraph ω).induce (V : Set (Vertex 2)))
          (unitCond ((openGraph ω).induce (V : Set (Vertex 2)))) Finset.univ θ ≤
            crossFlowBound L w k N := by
  -- the crossings
  obtain ⟨a0, a1, hA, ha0, ha1⟩ := exists_reachIn_of_hasOpenCrossing_one ha
  obtain ⟨b0, b1, hB, hb0, hb1⟩ := exists_reachIn_of_hasOpenCrossing_zero hb
  choose hs he hH hs0 he0 using fun i : Fin k => exists_reachIn_of_hasOpenCrossing_zero (hrow i)
  choose vs ve hV hvs1 hve1 using fun j : Fin k => exists_reachIn_of_hasOpenCrossing_one (hcol j)
  have hjk : ∀ j : Fin k, ((j : ℕ) : ℤ) * (w + 1) + w + 1 ≤ k * (w + 1) := by
    intro j
    have h := Nat.mul_le_mul_right (w + 1) (show (j : ℕ) + 1 ≤ k from j.isLt)
    have h' : (((((j : ℕ) + 1) * (w + 1) : ℕ)) : ℤ) ≤ ((k * (w + 1) : ℕ) : ℤ) := by
      exact_mod_cast h
    push_cast at h'
    linarith
  have hj0 : ∀ j : Fin k, (0 : ℤ) ≤ ((j : ℕ) : ℤ) * (w + 1) := fun j => by positivity
  -- meeting points
  choose p hpH hpA using fun i : Fin k => exists_reachIn_of_crossing (hH i) hA
    (ya := y.val 1 + (i : ℕ) * (w + 1)) (yb := y.val 1 + (i : ℕ) * (w + 1) + w)
    (xa := y.val 0) (xb := y.val 0 + w) (fun z hz => hz.2) (fun z hz => hz.1)
    (by rw [hs0 i]; exact hy0) (by rw [he0 i]; push_cast; linarith)
    (by rw [ha0]; linarith [hj0 i]) (by rw [ha1]; push_cast; linarith [hjk i])
  choose q hqH hqV using fun (i j : Fin k) => exists_reachIn_of_crossing (hH i) (hV j)
    (ya := y.val 1 + (i : ℕ) * (w + 1)) (yb := y.val 1 + (i : ℕ) * (w + 1) + w)
    (xa := x.val 0 + (j : ℕ) * (w + 1)) (xb := x.val 0 + (j : ℕ) * (w + 1) + w)
    (fun z hz => hz.2) (fun z hz => hz.1)
    (by rw [hs0 i]; linarith [hj0 j]) (by rw [he0 i]; push_cast; linarith [hjk j])
    (by rw [hvs1 j]; linarith [hj0 i]) (by rw [hve1 j]; push_cast; linarith [hjk i])
  choose r hrB hrV using fun j : Fin k => exists_reachIn_of_crossing hB (hV j)
    (ya := x.val 1) (yb := x.val 1 + w)
    (xa := x.val 0 + (j : ℕ) * (w + 1)) (xb := x.val 0 + (j : ℕ) * (w + 1) + w)
    (fun z hz => hz.2) (fun z hz => hz.1)
    (by rw [hb0]; linarith [hj0 j]) (by rw [hb1]; push_cast; linarith [hjk j])
    (by rw [hvs1 j]; exact hx1) (by rw [hve1 j]; push_cast; linarith)
  -- local links
  have hyC : ((openGraph ω).connectedComponentMk y.val).supp.Infinite := by
    rw [(SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 y.2]; exact hC
  have hxC : ((openGraph ω).connectedComponentMk x.val).supp.Infinite := by
    rw [(SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 x.2]; exact hC
  have hMy := wcSubRadius_lt_of_isWellConnected hN hwcy
  have hMx := wcSubRadius_lt_of_isWellConnected hN hwcx
  have hA0 := hA.start_mem
  have hB0 := hB.start_mem
  obtain ⟨ℓy, hℓy⟩ := exists_walk_of_isWellConnected_of_startsLongPath hN hwcy
    (x := y.val) (y := a0) (fun i => by simp)
    (by
      intro i
      fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue]
        rw [abs_le]
        obtain ⟨⟨h1, h2⟩, -⟩ := hA0
        constructor <;> linarith
      · simp only [Fin.mk_one, Fin.isValue]
        rw [ha0, sub_self, abs_zero]
        positivity)
    (startsLongPath_of_infinite _ hyC)
    (startsLongPath_of_reachIn hA 1 (by
      rw [ha0, ha1]
      linarith [show ((wcSubRadius 2 N : ℕ) : ℤ) < ((k * (w + 1) : ℕ) : ℤ) by
        exact_mod_cast hMy.trans hNH]))
  obtain ⟨ℓx, hℓx⟩ := exists_walk_of_isWellConnected_of_startsLongPath hN hwcx
    (x := x.val) (y := b0) (fun i => by simp)
    (by
      intro i
      fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue]
        rw [hb0, sub_self, abs_zero]
        positivity
      · simp only [Fin.mk_one, Fin.isValue]
        rw [abs_le]
        obtain ⟨-, h1, h2⟩ := hB0
        constructor <;> linarith)
    (startsLongPath_of_infinite _ hxC)
    (startsLongPath_of_reachIn hB 0 (by
      rw [hb0, hb1]
      linarith [show ((wcSubRadius 2 N : ℕ) : ℤ) < ((k * (w + 1) : ℕ) : ℤ) by
        exact_mod_cast hMx.trans hNH]))
  -- the walks
  choose WA hWA using hpA
  choose WH hWH using fun i j => (hpH i).symm.trans (hqH i j)
  choose WV hWV using fun i j => (hqV i j).symm.trans (hrV j)
  choose WB hWB using fun j => (hrB j).symm
  let γ : Fin k → Fin k → (openGraph ω).Walk y.val x.val := fun i j =>
    ℓy.append ((WA i).append ((WH i j).append ((WV i j).append ((WB j).append ℓx.reverse))))
  let RA := rectFinset (y.val 0) (y.val 1) w (k * (w + 1))
  let RB := rectFinset (x.val 0) (x.val 1) (k * (w + 1)) w
  let H := ℓy.support.toFinset ∪ RA ∪ RB ∪ ℓx.support.toFinset
  let Sh : Fin k → Finset (Vertex 2) := fun i =>
    rectFinset (-(L : ℤ)) (y.val 1 + (i : ℕ) * (w + 1)) (2 * L) w
  let Sv : Fin k → Finset (Vertex 2) := fun j =>
    rectFinset (x.val 0 + (j : ℕ) * (w + 1)) (-(L : ℤ)) w (2 * L)
  have hγ : ∀ i j, ∀ u ∈ (γ i j).support, u ∈ H ∨ u ∈ Sh i ∨ u ∈ Sv j := by
    intro i j u hu
    simp only [γ, SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_reverse,
      List.mem_reverse] at hu
    rcases hu with hu | hu | hu | hu | hu | hu
    · left
      simp [H, hu]
    · left
      have := hWA i u hu
      simp only [H, Finset.mem_union, RA, mem_rectFinset]
      exact Or.inl (Or.inl (Or.inr this))
    · right; left
      exact mem_rectFinset.2 (hWH i j u hu)
    · right; right
      exact mem_rectFinset.2 (hWV i j u hu)
    · left
      have := hWB j u hu
      simp only [H, Finset.mem_union, RB, mem_rectFinset]
      exact Or.inl (Or.inr this)
    · left
      simp [H, hu]
  have hSh : ∀ u i i', u ∈ Sh i → u ∈ Sh i' → i = i' := by
    intro u i i' hi hi'
    obtain ⟨-, h1, h2⟩ := mem_rectFinset.1 hi
    obtain ⟨-, h1', h2'⟩ := mem_rectFinset.1 hi'
    have := eq_of_window_overlap (a := ((i : ℕ) : ℤ)) (b := ((i' : ℕ) : ℤ)) (c := (w : ℤ))
      (t := u 1 - y.val 1) (by positivity)
      ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
    exact Fin.ext (by exact_mod_cast this)
  have hSv : ∀ u j j', u ∈ Sv j → u ∈ Sv j' → j = j' := by
    intro u j j' hj hj'
    obtain ⟨⟨h1, h2⟩, -⟩ := mem_rectFinset.1 hj
    obtain ⟨⟨h1', h2'⟩, -⟩ := mem_rectFinset.1 hj'
    have := eq_of_window_overlap (a := ((j : ℕ) : ℤ)) (b := ((j' : ℕ) : ℤ)) (c := (w : ℤ))
      (t := u 0 - x.val 0) (by positivity)
      ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
    exact Fin.ext (by exact_mod_cast this)
  let V : Finset (Vertex 2) :=
    Finset.univ.biUnion fun ij : Fin k × Fin k => (γ ij.1 ij.2).support.toFinset
  have hγV : ∀ i j, ∀ u ∈ (γ i j).support, u ∈ V := fun i j u hu =>
    Finset.mem_biUnion.2 ⟨(i, j), Finset.mem_univ _, List.mem_toFinset.2 hu⟩
  have hyV : y.val ∈ V := hγV ⟨0, hk⟩ ⟨0, hk⟩ _ (SimpleGraph.Walk.start_mem_support _)
  have hxV : x.val ∈ V := hγV ⟨0, hk⟩ ⟨0, hk⟩ _ (SimpleGraph.Walk.end_mem_support _)
  have hVC : ∀ z ∈ V, z ∈ C.supp := by
    intro z hz
    obtain ⟨ij, -, hz⟩ := Finset.mem_biUnion.1 hz
    exact mem_supp_of_mem_support y.2 _ (List.mem_toFinset.1 hz)
  obtain ⟨θ, hθ, hdiv, hE⟩ := exists_flow_energy_le_of_walk_family (openGraph ω) V 4
    (induce_openGraph_degree_le V) hyV hxV hk γ hγV H Sh Sv hSh hSv hγ
  refine ⟨V, hVC, hyV, hxV, θ, hθ, fun z => by convert hdiv z, hE.trans ?_⟩
  -- the energy bound
  set B := (4 * N + 1) * (2 * wcSubRadius 2 N + 1) ^ 2 with hBdef
  have hℓy' : ℓy.length ≤ B := by rw [hBdef]; convert hℓy using 2
  have hℓx' : ℓx.length ≤ B := by rw [hBdef]; convert hℓx using 2
  have hHcard : H.card ≤ 2 * (B + 1) + 2 * ((w + 1) * (k * (w + 1) + 1)) := by
    have h1 : ℓy.support.toFinset.card ≤ B + 1 :=
      (List.toFinset_card_le _).trans (by rw [SimpleGraph.Walk.length_support]; omega)
    have h2 : ℓx.support.toFinset.card ≤ B + 1 :=
      (List.toFinset_card_le _).trans (by rw [SimpleGraph.Walk.length_support]; omega)
    have h3 : RA.card ≤ (w + 1) * (k * (w + 1) + 1) := card_rectFinset_le _ _ _ _
    have h4 : RB.card ≤ (w + 1) * (k * (w + 1) + 1) :=
      (card_rectFinset_le _ _ _ _).trans (le_of_eq (Nat.mul_comm _ _))
    calc H.card ≤ ℓy.support.toFinset.card + RA.card + RB.card + ℓx.support.toFinset.card := by
          refine (Finset.card_union_le _ _).trans (Nat.add_le_add_right ?_ _)
          refine (Finset.card_union_le _ _).trans (Nat.add_le_add_right ?_ _)
          exact Finset.card_union_le _ _
      _ ≤ _ := by omega
  have hShcard : ∑ i, ((Sh i).card : ℝ) ≤ (k : ℝ) * ((2 * (L : ℝ) + 1) * ((w : ℝ) + 1)) := by
    calc ∑ i, ((Sh i).card : ℝ) ≤ ∑ _i : Fin k, ((2 * L + 1) * (w + 1) : ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          exact_mod_cast card_rectFinset_le _ _ _ _
      _ = _ := by simp
  have hSvcard : ∑ j, ((Sv j).card : ℝ) ≤ (k : ℝ) * ((2 * (L : ℝ) + 1) * ((w : ℝ) + 1)) := by
    calc ∑ j, ((Sv j).card : ℝ) ≤ ∑ _j : Fin k, ((2 * L + 1) * (w + 1) : ℝ) := by
          apply Finset.sum_le_sum
          intro j _
          have := card_rectFinset_le (x.val 0 + (j : ℕ) * (w + 1)) (-(L : ℤ)) w (2 * L)
          have h' : ((Sv j).card : ℝ) ≤ ((w + 1) * (2 * L + 1) : ℕ) := by exact_mod_cast this
          push_cast at h'
          linarith
      _ = _ := by simp
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hH' : (H.card : ℝ) ≤ 2 * ((B : ℝ) + 1) + 2 * (((w + 1) * (k * (w + 1) + 1) : ℕ) : ℝ) := by
    exact_mod_cast hHcard
  have hfrac : 4 / (k : ℝ) ^ 2 * (∑ i, ((Sh i).card : ℝ) + ∑ j, ((Sv j).card : ℝ)) ≤
      8 * (2 * (L : ℝ) + 1) * ((w : ℝ) + 1) / k := by
    calc 4 / (k : ℝ) ^ 2 * (∑ i, ((Sh i).card : ℝ) + ∑ j, ((Sv j).card : ℝ))
        ≤ 4 / (k : ℝ) ^ 2 * ((k : ℝ) * ((2 * (L : ℝ) + 1) * ((w : ℝ) + 1)) +
            (k : ℝ) * ((2 * (L : ℝ) + 1) * ((w : ℝ) + 1))) := by
          gcongr
      _ = 8 * (2 * (L : ℝ) + 1) * ((w : ℝ) + 1) / k := by
          field_simp
          ring
  unfold crossFlowBound
  rw [← hBdef]
  push_cast
  push_cast at hH'
  nlinarith

end Rigidity.Proofs.Section5
