import «section 8».HmFields

/-! `h_m` is multiplicative.

For bounded charts `a`, `b`, the lattice part of `a × b` with weight `w` is the disjoint union, over
the pairs of weights `(w₁, w₂)` of `a` and `b` with `w₁ w₂ = w`, of the products of the lattice
parts of weights `w₁`, `w₂` (`latticeFibre_product`). The class of a product of RES charts is the
product of the classes, and the exponents add (`ratValue_mul`), so
`hmValue (a × b) = hmValue a · hmValue b` (`hmValue_product`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace DiamondIntegral.Section8.Hm

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4 RVMeasuredCharts FiniteTupleBlocks
open DiamondIntegral.Section5 DiamondIntegral.Section5.PuiseuxOriginal DiamondIntegral.Section8.PuiseuxValues
open DiamondIntegral.Section8.RESPieces DiamondIntegral.Section8.GammaCells
open RVMeasuredProduct RVMeasuredProductProperties RVRealProducts

variable (P : PuiseuxAmbient)

local notation "Γ" => Values.Gamma (M := P.N)
local notation "π" => uniformizerValue P

section product

variable {k l : ℕ} (a : Chart (base P) k) (b : Chart (base P) l)

theorem product_weight (u : Fin (b.arity + a.arity) → P.N) :
    (product a b).correctedWeight u =
      a.correctedWeight (u ∘ headIndex b.arity a.arity) * b.correctedWeight (u ∘ tailIndex b.arity a.arity) := by
  conv_lhs => rw [← join_reconstruct b.arity a.arity u]
  exact product_weight_join a b _ _

theorem latticeDomain_product (m : ℕ) (u : Fin (b.arity + a.arity) → P.N) :
    u ∈ latticeDomain P (product a b) m ↔
      u ∘ headIndex b.arity a.arity ∈ latticeDomain P a m ∧
        u ∘ tailIndex b.arity a.arity ∈ latticeDomain P b m := by
  constructor
  · rintro ⟨⟨h1, h2⟩, hl⟩
    exact ⟨⟨h1, fun i => hl _⟩, ⟨h2, fun i => hl _⟩⟩
  · rintro ⟨⟨h1, hl1⟩, ⟨h2, hl2⟩⟩
    exact ⟨⟨h1, h2⟩, GammaBoundedProducts.all_coordinates b.arity a.arity
      (fun t => InLattice π m (codeValue t)) u hl1 hl2⟩

/-- The pairs of weights of `a` and `b` with product `w`. -/
def weightPairs (ha : RVMeasuredBounds.DomainBounded a) (hb : RVMeasuredBounds.DomainBounded b)
    (m : ℕ+) (w : Γ) : Finset (Γ × Γ) :=
  (weights P a ha m ×ˢ weights P b hb m).filter fun p => p.1 * p.2 = w

theorem latticeFibre_product (ha : RVMeasuredBounds.DomainBounded a)
    (hb : RVMeasuredBounds.DomainBounded b) (m : ℕ+) (w : Γ) :
    latticeFibre P (product a b) m w =
      ⋃ p ∈ weightPairs P a b ha hb m w, productSet (latticeFibre P a m p.1) (latticeFibre P b m p.2) := by
  ext u
  simp only [Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨hu, hw⟩
    obtain ⟨h1, h2⟩ := (latticeDomain_product P a b m u).mp hu
    refine ⟨(a.correctedWeight (u ∘ headIndex b.arity a.arity),
      b.correctedWeight (u ∘ tailIndex b.arity a.arity)), ?_, ⟨h1, rfl⟩, ⟨h2, rfl⟩⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨(mem_weights P a ha m _).mpr ⟨_, h1, rfl⟩,
      (mem_weights P b hb m _).mpr ⟨_, h2, rfl⟩⟩, ?_⟩
    rw [← product_weight]
    exact hw
  · rintro ⟨p, hp, ⟨h1, hw1⟩, ⟨h2, hw2⟩⟩
    refine ⟨(latticeDomain_product P a b m u).mpr ⟨h1, h2⟩, ?_⟩
    rw [product_weight, hw1, hw2]
    exact (Finset.mem_filter.mp hp).2

theorem weightPairs_disjoint (ha : RVMeasuredBounds.DomainBounded a)
    (hb : RVMeasuredBounds.DomainBounded b) (m : ℕ+) (w : Γ) :
    ((weightPairs P a b ha hb m w : Finset (Γ × Γ)) : Set (Γ × Γ)).PairwiseDisjoint
      (fun p => productSet (latticeFibre P a m p.1) (latticeFibre P b m p.2)) := by
  intro p _ q _ hpq
  rw [Function.onFun, Set.disjoint_left]
  rintro u ⟨⟨_, hp1⟩, ⟨_, hp2⟩⟩ ⟨⟨_, hq1⟩, ⟨_, hq2⟩⟩
  exact hpq (Prod.ext (hp1.symm.trans hq1) (hp2.symm.trans hq2))

theorem class_fibre_product (ha : RVMeasuredBounds.DomainBounded a)
    (hb : RVMeasuredBounds.DomainBounded b) (hab : RVMeasuredBounds.DomainBounded (product a b))
    (m : ℕ+) (w : Γ) :
    nativeRESChartClass (fibreChart P (product a b) hab m w) =
      ∑ p ∈ weightPairs P a b ha hb m w,
        nativeRESChartClass (fibreChart P a ha m p.1) * nativeRESChartClass (fibreChart P b hb m p.2) := by
  have hdom : (fibreChart P (product a b) hab m w).domain =
      ⋃ p ∈ weightPairs P a b ha hb m w, productSet (latticeFibre P a m p.1) (latticeFibre P b m p.2) :=
    (fibreChart_domain P _ hab m w).trans (latticeFibre_product P a b ha hb m w)
  have hdef : ∀ p ∈ weightPairs P a b ha hb m w, DefinableOverBase (base P)
      (fun _ : Fin (b.arity + a.arity) => .rv) (productSet (latticeFibre P a m p.1) (latticeFibre P b m p.2)) :=
    fun p _ => productSet_definable (base P) _ _ (latticeFibre_definable' P a ha m p.1)
      (latticeFibre_definable' P b hb m p.2)
  have hsub : ∀ p ∈ weightPairs P a b ha hb m w,
      productSet (latticeFibre P a m p.1) (latticeFibre P b m p.2) ⊆
        (fibreChart P (product a b) hab m w).domain := fun p hp u hu => by
    rw [hdom]; exact Set.mem_biUnion hp hu
  rw [← classOn_domain (fibreChart P (product a b) hab m w), hdom,
    classOn_biUnion _ _ _ hdef hsub (weightPairs_disjoint P a b ha hb m w)]
  refine Finset.sum_congr rfl fun p hp => ?_
  exact (classOn_eq_of_domain (fibreChart P (product a b) hab m w) _ (hdef p hp) (hsub p hp)
    (resProduct (fibreChart P a ha m p.1) (fibreChart P b hb m p.2)) rfl
    (fun u => by simp only [Fin.cast_refl, Function.comp_id]; rfl)).trans
    (nativeRESChartClass_product _ _)

theorem weight_rational (ha : RVMeasuredBounds.DomainBounded a) (m : ℕ+) {w : Γ}
    (hw : w ∈ weights P a ha m) : IsRationalValue π w := by
  have hw' : w ∈ a.correctedWeight '' latticeDomain P a m := by
    obtain ⟨u, hu⟩ := (mem_weights P a ha m w).mp hw
    exact ⟨u, hu.1, hu.2⟩
  obtain ⟨q, rfl⟩ := latticeWeight_rational P (bdd P a ha) m.ne_zero hw'
  exact isRationalValue_qpow _ q

/-- **`h_m` is multiplicative.** -/
theorem hmValue_product (ha : RVMeasuredBounds.DomainBounded a)
    (hb : RVMeasuredBounds.DomainBounded b) (hab : RVMeasuredBounds.DomainBounded (product a b))
    (m : ℕ+) : hmValue P (product a b) hab m = hmValue P a ha m * hmValue P b hb m := by
  let S : Finset Γ := (weights P a ha m ×ˢ weights P b hb m).image fun p => p.1 * p.2
  have hS : weights P (product a b) hab m ⊆ S := by
    intro w hw
    obtain ⟨u, hu⟩ := (mem_weights P _ hab m w).mp hw
    rw [latticeFibre_product P a b ha hb m w] at hu
    simp only [Set.mem_iUnion, exists_prop] at hu
    obtain ⟨p, hp, -⟩ := hu
    exact Finset.mem_image.mpr ⟨p, (Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2⟩
  have hterm : ∀ w, hmTerm P (product a b) hab m w =
      ∑ p ∈ weightPairs P a b ha hb m w, hmTerm P a ha m p.1 * hmTerm P b hb m p.2 := by
    intro w
    have hsingle : ∀ (c : ℚ) (s : Finset (Γ × Γ)) (f : Γ × Γ → EquivariantVariety.ModifiedRing),
        AddMonoidAlgebra.single c (∑ x ∈ s, f x) = ∑ x ∈ s, AddMonoidAlgebra.single c (f x) :=
      fun c s f => map_sum (AddMonoidAlgebra.singleAddHom c) f s
    unfold hmTerm
    rw [class_fibre_product P a b ha hb hab m w, map_sum, hsingle]
    refine Finset.sum_congr rfl fun p hp => ?_
    obtain ⟨hp1, hpw⟩ := Finset.mem_filter.mp hp
    obtain ⟨hw1, hw2⟩ := Finset.mem_product.mp hp1
    rw [AddMonoidAlgebra.single_mul_single, map_mul, ← hpw,
      ratValue_mul (one_lt_uniformizerValue P) (weight_rational P a ha m hw1)
        (weight_rational P b hb m hw2)]
    congr 1
    ring
  rw [hmValue_eq_sum P _ hab m S hS]
  simp only [hterm, weightPairs]
  rw [Finset.sum_fiberwise_of_maps_to (s := weights P a ha m ×ˢ weights P b hb m) (t := S)
    (g := fun p => p.1 * p.2) (fun p hp => Finset.mem_image_of_mem _ hp)
    (f := fun p => hmTerm P a ha m p.1 * hmTerm P b hb m p.2)]
  rw [Finset.sum_product, hmValue, hmValue, Finset.sum_mul_sum]

end product

end DiamondIntegral.Section8.Hm
