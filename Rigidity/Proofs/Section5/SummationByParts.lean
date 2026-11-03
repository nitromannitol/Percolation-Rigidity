import Rigidity.Steps.Section5.MeanZeroRepresentation

/-! # Lemma 5.6, summation by parts (the discrete divergence theorem)

If an antisymmetric `F` supported in a finite set `S` of oriented pairs has divergence
`Σ_b F(a, b) = g(a)`, then `Σ_a g(a) k(a) = ½ Σ_{(a, b) ∈ S} F(a, b) (k(a) - k(b))`.

Both sides are sums over the finite set `U × U`, where `U` is the set of first coordinates of `S`
(by antisymmetry it also contains the second coordinates of the support of `F`); exchanging the
order of summation in the term `F(a, b) k(b)` and using antisymmetry gives the identity. -/

open Classical

namespace Rigidity.Proofs.Section5

/-- Summation by parts (corrected draft, proof of Lemma 5.6, L1601). -/
theorem summationByParts : Steps.Section5.SummationByPartsStep := by
  intro α F g S hanti hS hdiv k
  set U : Finset α := S.image Prod.fst
  have hfst : ∀ a b, F a b ≠ 0 → a ∈ U := fun a b h =>
    Finset.mem_image.2 ⟨(a, b), hS a b h, rfl⟩
  have hsnd : ∀ a b, F a b ≠ 0 → b ∈ U := fun a b h =>
    hfst b a (by rw [hanti] at h; exact neg_ne_zero.1 h)
  have hg : ∀ a, g a = ∑ b ∈ U, F a b := fun a => by
    rw [← hdiv a]
    exact finsum_eq_sum_of_support_subset _ fun b hb => hsnd a b hb
  have hLHS : ∑ᶠ a, g a * k a = ∑ a ∈ U, ∑ b ∈ U, F a b * k a := by
    rw [finsum_eq_sum_of_support_subset _ (s := U) fun a ha => ?_]
    · exact Finset.sum_congr rfl fun a _ => by rw [hg a, Finset.sum_mul]
    · by_contra haU
      refine ha ?_
      show g a * k a = 0
      rw [hg a, Finset.sum_eq_zero fun b _ => ?_, zero_mul]
      by_contra hb
      exact haU (hfst a b hb)
  have hsupp : ∀ T : Finset (α × α), (∀ a b, F a b ≠ 0 → (a, b) ∈ T) →
      ∑ e ∈ T, F e.1 e.2 * (k e.1 - k e.2) = ∑ᶠ e : α × α, F e.1 e.2 * (k e.1 - k e.2) :=
    fun T hT => (finsum_eq_sum_of_support_subset _ fun e he =>
      hT e.1 e.2 (left_ne_zero_of_mul (Function.mem_support.1 he))).symm
  rw [hLHS, hsupp S hS, ← hsupp (U ×ˢ U) fun a b h =>
    Finset.mem_product.2 ⟨hfst a b h, hsnd a b h⟩, Finset.sum_product]
  have hswap : ∑ a ∈ U, ∑ b ∈ U, F a b * k b = -∑ a ∈ U, ∑ b ∈ U, F a b * k a := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun b _ => by rw [hanti, neg_mul]
  simp only [mul_sub, Finset.sum_sub_distrib, hswap]
  ring

end Rigidity.Proofs.Section5
