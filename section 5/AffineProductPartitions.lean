import «section 5».AffineImmersedProductPresentations
import «section 5».ImmersedPresentationLoci

/-! Products of finite immersed presentations give finite immersed
presentations of the actual product locus. Their geometric values multiply. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory EquivariantVariety Topology TopologicalSpace
variable {n m : ℕ} (q : Fin n → ℚ) (r : Fin m → ℚ)

def affineProductLocus (D : Set (PrimeSpectrum (MvPolynomial (Fin n) ℂ)))
    (E : Set (PrimeSpectrum (MvPolynomial (Fin m) ℂ))) : Set (PrimeSpectrum (MvPolynomial (Fin (n + m)) ℂ)) :=
  (rationalAffineLeft q r).hom ⁻¹' D ∩ (rationalAffineRight q r).hom ⁻¹' E

theorem affineProductLocus_constructible {D : Set (PrimeSpectrum (MvPolynomial (Fin n) ℂ))}
    {E : Set (PrimeSpectrum (MvPolynomial (Fin m) ℂ))} (hD : IsConstructible D) (hE : IsConstructible E) :
    IsConstructible (affineProductLocus q r D E) := by
  letI := (rationalAffineObject (Fin.append q r)).noetherian
  exact (hD.preimage (rationalAffineLeft q r).hom.continuous
    (fun _ _ _ => fun _ _ _ => NoetherianSpace.isCompact _)).inter
    (hE.preimage (rationalAffineRight q r).hom.continuous
      (fun _ _ _ => fun _ _ _ => NoetherianSpace.isCompact _))

theorem affineProductLocus_invariant {D : Set (PrimeSpectrum (MvPolynomial (Fin n) ℂ))}
    {E : Set (PrimeSpectrum (MvPolynomial (Fin m) ℂ))}
    (hiD : (rationalAffineObject q).Invariant D) (hiE : (rationalAffineObject r).Invariant E) :
    (rationalAffineObject (Fin.append q r)).Invariant (affineProductLocus q r D E) := by
  intro η z
  have hL := congrArg (fun h => h z) ((rationalAffineLeft q r).equivariant η)
  have hR := congrArg (fun h => h z) ((rationalAffineRight q r).equivariant η)
  change (rationalAffineLeft q r).hom (schemePointAction (rationalAffineObject (Fin.append q r)).action η z) =
    schemePointAction (rationalAffineObject q).action η ((rationalAffineLeft q r).hom z) at hL
  change (rationalAffineRight q r).hom (schemePointAction (rationalAffineObject (Fin.append q r)).action η z) =
    schemePointAction (rationalAffineObject r).action η ((rationalAffineRight q r).hom z) at hR
  change (_ ∈ D ∧ _ ∈ E) ↔ (_ ∈ D ∧ _ ∈ E)
  rw [hL, hR]
  exact and_congr (hiD η _) (hiE η _)

def affineProductImmersedPresentation
    {D : Set (PrimeSpectrum (MvPolynomial (Fin n) ℂ))} {E : Set (PrimeSpectrum (MvPolynomial (Fin m) ℂ))}
    (c : ImmersedPresentation (rationalAffineObject q) D)
    (d : ImmersedPresentation (rationalAffineObject r) E) :
    ImmersedPresentation (rationalAffineObject (Fin.append q r)) (affineProductLocus q r D E) := by
  letI := c.finite
  letI := d.finite
  letI (i : c.index) := c.immersion i
  letI (j : d.index) := d.immersion j
  refine {
    index := c.index × d.index
    finite := inferInstance
    piece := fun p => affineImmersedProductObject q r (c.inclusion p.1) (d.inclusion p.2)
    inclusion := fun p => affineImmersedProductInclusion q r (c.inclusion p.1) (d.inclusion p.2)
    immersion := fun p => affineImmersedProductMap_immersion q r (c.inclusion p.1) (d.inclusion p.2)
    contained := ?_
    partition := ?_ }
  · intro p z hz
    change z ∈ Set.range (affineImmersedProductMap q r (c.inclusion p.1) (d.inclusion p.2)) at hz
    rw [affineImmersedProductMap_range] at hz
    exact ⟨c.contained p.1 hz.1, d.contained p.2 hz.2⟩
  · intro z
    have he (p : c.index × d.index) : z ∈ Set.range (affineImmersedProductInclusion q r
        (c.inclusion p.1) (d.inclusion p.2)).hom ↔
        (rationalAffineLeft q r).hom z ∈ Set.range (c.inclusion p.1).hom ∧
          (rationalAffineRight q r).hom z ∈ Set.range (d.inclusion p.2).hom := by
      change z ∈ Set.range (affineImmersedProductMap q r (c.inclusion p.1) (d.inclusion p.2)) ↔ _
      rw [affineImmersedProductMap_range]
      rfl
    constructor
    · intro hz
      obtain ⟨i, hi, hui⟩ := (c.partition ((rationalAffineLeft q r).hom z)).mp hz.1
      obtain ⟨j, hj, huj⟩ := (d.partition ((rationalAffineRight q r).hom z)).mp hz.2
      refine ⟨(i,j), (he (i,j)).mpr ⟨hi,hj⟩, ?_⟩
      intro p hp
      have hh := (he p).mp hp
      exact Prod.ext (hui p.1 hh.1) (huj p.2 hh.2)
    · rintro ⟨p, hp, _⟩
      have hh := (he p).mp hp
      exact ⟨c.contained p.1 hh.1, d.contained p.2 hh.2⟩

theorem affineProductImmersedPresentation_value
    {D : Set (PrimeSpectrum (MvPolynomial (Fin n) ℂ))} {E : Set (PrimeSpectrum (MvPolynomial (Fin m) ℂ))}
    (c : ImmersedPresentation (rationalAffineObject q) D)
    (d : ImmersedPresentation (rationalAffineObject r) E) :
    (affineProductImmersedPresentation q r c d).value = c.value * d.value := by
  letI := c.finite
  letI := d.finite
  letI (i : c.index) := c.immersion i
  letI (j : d.index) := d.immersion j
  change (∑ p : c.index × d.index,
    objectClass (affineImmersedProductObject q r (c.inclusion p.1) (d.inclusion p.2))) =
      (∑ i, objectClass (c.piece i)) * (∑ j, objectClass (d.piece j))
  simp_rw [affineImmersedProductObject_class]
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]

theorem constructibleClass_affine_product
    (D : Set (PrimeSpectrum (MvPolynomial (Fin n) ℂ))) (E : Set (PrimeSpectrum (MvPolynomial (Fin m) ℂ)))
    (hD : IsConstructible D) (hE : IsConstructible E)
    (hiD : (rationalAffineObject q).Invariant D) (hiE : (rationalAffineObject r).Invariant E) :
    constructibleClass (rationalAffineObject (Fin.append q r)) (affineProductLocus q r D E)
      (affineProductLocus_constructible q r hD hE) (affineProductLocus_invariant q r hiD hiE) =
      constructibleClass (rationalAffineObject q) D hD hiD * constructibleClass (rationalAffineObject r) E hE hiE := by
  let c := Classical.choice (invariant_constructible_immersed_presentation (rationalAffineObject q) D hD hiD)
  let d := Classical.choice (invariant_constructible_immersed_presentation (rationalAffineObject r) E hE hiE)
  rw [constructibleClass_eq_presentation _ _ _ _ (affineProductImmersedPresentation q r c d),
    affineProductImmersedPresentation_value]
  rfl

end DiamondIntegral.Section5
