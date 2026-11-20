import Rigidity.Proofs.Section5.PathFlowLoad

/-!
# Unit flows from doubly indexed walk families

Let `γ i j`, `i j : Fin k`, be walks from `y` to `x` inside a finite vertex set `V`, and suppose
that every vertex of `γ i j` lies in a common set `H`, in the `i`-th set of a disjoint family
`Sh`, or in the `j`-th set of a disjoint family `Sv`. Averaging the paths obtained from the walks
gives a unit flow from `y` to `x` in the graph induced on `V`. A vertex outside `H` meets at most
`2k` of the `k²` walks, so the energy of the flow is at most
`D (|H| + 4 k⁻² (Σ |Sh i| + Σ |Sv j|))` when the induced degrees are at most `D`.
-/

open SimpleGraph LatticeProb.Network
open scoped Classical

namespace Rigidity.Proofs.Section5

/-- The number of members of a walk family whose support contains a vertex of a set `S` is at
most the number of indices whose set contains it, when `S` covers the walks. -/
theorem card_filter_mem_support_le {α ι κ : Type} [Fintype ι] [Fintype κ] {y x : α}
    {G : SimpleGraph α} (γ : ι → κ → G.Walk y x) (H : Finset α) (Sh : ι → Finset α)
    (Sv : κ → Finset α) (hγ : ∀ i j, ∀ u ∈ (γ i j).support, u ∈ H ∨ u ∈ Sh i ∨ u ∈ Sv j)
    {u : α} (hu : u ∉ H) :
    (Finset.univ.filter fun ij : ι × κ => u ∈ (γ ij.1 ij.2).support).card ≤
      (Finset.univ.filter fun i => u ∈ Sh i).card * Fintype.card κ +
        Fintype.card ι * (Finset.univ.filter fun j => u ∈ Sv j).card := by
  calc
    _ ≤ ((Finset.univ.filter fun i => u ∈ Sh i) ×ˢ (Finset.univ : Finset κ) ∪
          (Finset.univ : Finset ι) ×ˢ (Finset.univ.filter fun j => u ∈ Sv j)).card := by
      apply Finset.card_le_card
      intro ij hij
      have hmem := (Finset.mem_filter.1 hij).2
      rcases hγ ij.1 ij.2 u hmem with h | h | h
      · exact absurd h hu
      · exact Finset.mem_union_left _ (Finset.mem_product.2
          ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩, Finset.mem_univ _⟩)
      · exact Finset.mem_union_right _ (Finset.mem_product.2
          ⟨Finset.mem_univ _, Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩⟩)
    _ ≤ _ := by
      refine (Finset.card_union_le _ _).trans ?_
      rw [Finset.card_product, Finset.card_product, Finset.card_univ, Finset.card_univ]

/-- The square of a fraction of at most `k²` out of `k²` is at most one plus a nonnegative
number. -/
theorem sq_div_sq_le_one_add {n k c : ℝ} (hn0 : 0 ≤ n) (hn : n ≤ k * k) (hk : 0 < k)
    (hc : 0 ≤ c) : (n / k ^ 2) ^ 2 ≤ 1 + c := by
  have hk2 : 0 < k ^ 2 := by positivity
  have hle : n / k ^ 2 ≤ 1 := by
    rw [div_le_one hk2]
    nlinarith
  have h0 : 0 ≤ n / k ^ 2 := by positivity
  nlinarith

/-- A count `0 ≤ n ≤ a k + k b` with `a, b ≤ 1` has `(n / k²)² ≤ 4 (a + b) / k²`. -/
theorem sq_div_sq_le_four_div {n k a b : ℝ} (hn0 : 0 ≤ n) (hn : n ≤ a * k + k * b) (hk : 0 < k)
    (ha1 : a ≤ 1) (hb1 : b ≤ 1) :
    (n / k ^ 2) ^ 2 ≤ 4 / k ^ 2 * (a + b) := by
  have hk2 : 0 < k ^ 2 := by positivity
  have hfrac : n / k ^ 2 ≤ (a + b) / k := by
    rw [div_le_div_iff₀ hk2 hk]
    nlinarith
  have hfrac0 : 0 ≤ n / k ^ 2 := by positivity
  calc (n / k ^ 2) ^ 2 ≤ ((a + b) / k) ^ 2 := by gcongr
    _ = (a + b) ^ 2 / k ^ 2 := by ring
    _ ≤ 4 * (a + b) / k ^ 2 := by
        apply div_le_div_of_nonneg_right _ hk2.le
        nlinarith
    _ = 4 / k ^ 2 * (a + b) := by ring

/-- **Flows from doubly indexed walk families.** -/
theorem exists_flow_energy_le_of_walk_family {α : Type} (G : SimpleGraph α)
    (V : Finset α) (D : ℕ) (hdeg : ∀ u : V, (G.induce (V : Set α)).degree u ≤ D)
    {y x : α} (hy : y ∈ V) (hx : x ∈ V) {k : ℕ} (hk : 0 < k)
    (γ : Fin k → Fin k → G.Walk y x) (hγV : ∀ i j, ∀ u ∈ (γ i j).support, u ∈ V)
    (H : Finset α) (Sh Sv : Fin k → Finset α)
    (hSh : ∀ u i i', u ∈ Sh i → u ∈ Sh i' → i = i')
    (hSv : ∀ u j j', u ∈ Sv j → u ∈ Sv j' → j = j')
    (hγ : ∀ i j, ∀ u ∈ (γ i j).support, u ∈ H ∨ u ∈ Sh i ∨ u ∈ Sv j) :
    ∃ θ : V → V → ℝ, IsFlow (G.induce (V : Set α)) θ ∧
      (∀ z, divergence (G.induce (V : Set α)) θ z =
        (if z = ⟨y, hy⟩ then 1 else 0) - (if z = ⟨x, hx⟩ then 1 else 0)) ∧
      flowEnergyOn (G.induce (V : Set α)) (unitCond (G.induce (V : Set α))) Finset.univ θ ≤
        D * ((H.card : ℝ) +
          4 / (k : ℝ) ^ 2 * (∑ i, ((Sh i).card : ℝ) + ∑ j, ((Sv j).card : ℝ))) := by
  set G' := G.induce (V : Set α) with hG'
  let p : Fin k × Fin k → G'.Walk ⟨y, hy⟩ ⟨x, hx⟩ := fun ij =>
    ((γ ij.1 ij.2).induce (V : Set α) (hγV ij.1 ij.2)).bypass
  have hp : ∀ ij ∈ (Finset.univ : Finset (Fin k × Fin k)), (p ij).IsPath :=
    fun ij _ => Walk.bypass_isPath _
  have hs : (Finset.univ : Finset (Fin k × Fin k)).Nonempty :=
    ⟨(⟨0, hk⟩, ⟨0, hk⟩), Finset.mem_univ _⟩
  obtain ⟨θ, hθ, hdiv, hE⟩ := exists_flow_energy_le_path_edge_fractions G' Finset.univ hs p hp
  refine ⟨θ, hθ, fun z => by convert hdiv z, hE.trans ?_⟩
  let n : Set.Elem (V : Set α) → ℕ := fun u =>
    (Finset.univ.filter fun ij : Fin k × Fin k => u.val ∈ (γ ij.1 ij.2).support).card
  let a : Set.Elem (V : Set α) → ℕ := fun u => (Finset.univ.filter fun i => u.val ∈ Sh i).card
  let b : Set.Elem (V : Set α) → ℕ := fun u => (Finset.univ.filter fun j => u.val ∈ Sv j).card
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hcnt : ∀ (u v : (V : Set α)), (Finset.univ.filter fun ij : Fin k × Fin k =>
      s(u, v) ∈ (p ij).edges).card ≤ n u := by
    intro u v
    apply Finset.card_le_card
    intro ij hij
    have he := (Finset.mem_filter.1 hij).2
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    have hu := Walk.fst_mem_support_of_mem_edges _ he
    have hu' := Walk.support_bypass_subset_support _ hu
    rw [Walk.support_induce] at hu'
    exact (List.mem_attachWith _ _).1 hu'
  have hK : ((Finset.univ : Finset (Fin k × Fin k)).card : ℝ) = (k : ℝ) ^ 2 := by
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
    push_cast
    ring
  have hnK : ∀ u : (V : Set α), n u ≤ k * k := by
    intro u
    calc n u ≤ (Finset.univ : Finset (Fin k × Fin k)).card := Finset.card_le_card
          (Finset.filter_subset _ _)
      _ = k * k := by rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  have ha1 : ∀ u : (V : Set α), a u ≤ 1 := fun u => Finset.card_le_one.2 fun i hi i' hi' =>
    hSh u.val i i' (Finset.mem_filter.1 hi).2 (Finset.mem_filter.1 hi').2
  have hb1 : ∀ u : (V : Set α), b u ≤ 1 := fun u => Finset.card_le_one.2 fun j hj j' hj' =>
    hSv u.val j j' (Finset.mem_filter.1 hj).2 (Finset.mem_filter.1 hj').2
  have hkk : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
  have hpt : ∀ u : (V : Set α), ((n u : ℝ) / (k : ℝ) ^ 2) ^ 2 ≤
      (if u.val ∈ H then 1 else 0) + 4 / (k : ℝ) ^ 2 * ((a u : ℝ) + b u) := by
    intro u
    by_cases huH : u.val ∈ H
    · simp only [huH, if_true]
      exact sq_div_sq_le_one_add (Nat.cast_nonneg _) (by exact_mod_cast hnK u) hk'
        (by positivity)
    · simp only [huH, if_false, zero_add]
      have hn := card_filter_mem_support_le γ H Sh Sv hγ huH
      rw [Fintype.card_fin] at hn
      exact sq_div_sq_le_four_div (Nat.cast_nonneg _) (by exact_mod_cast hn) hk'
        (by exact_mod_cast ha1 u) (by exact_mod_cast hb1 u)
  have hsumH : ∑ u : (V : Set α), (if u.val ∈ H then (1 : ℝ) else 0) ≤ H.card := by
    rw [Finset.sum_boole]
    exact_mod_cast Finset.card_le_card_of_injOn (fun u : (V : Set α) => u.val)
      (fun u hu => (Finset.mem_filter.1 hu).2)
      (fun u _ v _ h => Subtype.ext h)
  have hsuma : ∑ u : (V : Set α), (a u : ℝ) ≤ ∑ i, ((Sh i).card : ℝ) := by
    have : ∑ u : (V : Set α), (a u : ℝ) =
        ∑ i, ((Finset.univ.filter fun u : (V : Set α) => u.val ∈ Sh i).card : ℝ) := by
      simp only [a, Finset.card_filter, Nat.cast_sum]
      rw [Finset.sum_comm]
    rw [this]
    apply Finset.sum_le_sum
    intro i _
    exact_mod_cast Finset.card_le_card_of_injOn (fun u : (V : Set α) => u.val)
      (fun u hu => (Finset.mem_filter.1 hu).2)
      (fun u _ v _ h => Subtype.ext h)
  have hsumb : ∑ u : (V : Set α), (b u : ℝ) ≤ ∑ j, ((Sv j).card : ℝ) := by
    have : ∑ u : (V : Set α), (b u : ℝ) =
        ∑ j, ((Finset.univ.filter fun u : (V : Set α) => u.val ∈ Sv j).card : ℝ) := by
      simp only [b, Finset.card_filter, Nat.cast_sum]
      rw [Finset.sum_comm]
    rw [this]
    apply Finset.sum_le_sum
    intro j _
    exact_mod_cast Finset.card_le_card_of_injOn (fun u : (V : Set α) => u.val)
      (fun u hu => (Finset.mem_filter.1 hu).2)
      (fun u _ v _ h => Subtype.ext h)
  calc
    _ ≤ ∑ u : (V : Set α), ∑ _v ∈ G'.neighborFinset u, ((n u : ℝ) / (k : ℝ) ^ 2) ^ 2 := by
      apply Finset.sum_le_sum
      intro u _
      apply Finset.sum_le_sum
      intro v _
      rw [hK]
      gcongr
      convert hcnt u v
      exact rfl
    _ = ∑ u : (V : Set α), (G'.degree u : ℝ) * ((n u : ℝ) / (k : ℝ) ^ 2) ^ 2 := by
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.sum_const, nsmul_eq_mul, SimpleGraph.card_neighborFinset_eq_degree]
    _ ≤ ∑ u : (V : Set α), (D : ℝ) * ((if u.val ∈ H then 1 else 0) +
          4 / (k : ℝ) ^ 2 * ((a u : ℝ) + b u)) := by
      apply Finset.sum_le_sum
      intro u _
      have hd : (G'.degree u : ℝ) ≤ D := by exact_mod_cast hdeg u
      have h0 : 0 ≤ ((n u : ℝ) / (k : ℝ) ^ 2) ^ 2 := by positivity
      calc (G'.degree u : ℝ) * ((n u : ℝ) / (k : ℝ) ^ 2) ^ 2
          ≤ (D : ℝ) * ((n u : ℝ) / (k : ℝ) ^ 2) ^ 2 := by gcongr
        _ ≤ _ := by gcongr; exact hpt u
    _ = (D : ℝ) * (∑ u : (V : Set α), (if u.val ∈ H then (1 : ℝ) else 0) +
          4 / (k : ℝ) ^ 2 * (∑ u : (V : Set α), (a u : ℝ) + ∑ u : (V : Set α), (b u : ℝ))) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_add_distrib]
    _ ≤ _ := by
      gcongr

end Rigidity.Proofs.Section5
