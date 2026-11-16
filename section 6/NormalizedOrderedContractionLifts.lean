import «section 6».BinaryContractionsAnyOrder

/-! Include the paper's actual preliminary normalization in the full
ordered lift. Its map on the original proper source is a proper
homeomorphism with the approved almost-everywhere unit total Jacobian. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r q : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S}
namespace ZeroCenteredData

def normalizedOrderedMap (D : ZeroCenteredData A) {e : Equiv.Perm (Fin n)}
    {U : DefSet (rawMixedSpace (M := M) 0 q) S}
    {T : OrderedStandardContractionProgram (G := G) S (reindexedVFSet D.map.image e) U}
    (V : OrderedStandardContractionLift T) : Map A V.originalTarget :=
  V.originalMap.comp D.bijection

theorem normalizedOrderedMap_homeomorphism
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (D : ZeroCenteredData A) {e : Equiv.Perm (Fin n)}
    {U : DefSet (rawMixedSpace (M := M) 0 q) S}
    {T : OrderedStandardContractionProgram (G := G) S (reindexedVFSet D.map.image e) U}
    (V : OrderedStandardContractionLift T) : ProperCovariantHomeomorphism (D.normalizedOrderedMap V) :=
  lemma_6_9 h00 hc linear hκ hs hv hsmall hΓ (D.properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ)
    (V.originalMap_homeomorphism h00 hc linear hκ hs hv hsmall hΓ (D.image_properInvariant h00 hc hκ hs hv))

theorem normalizedOrderedMap_generic_unit
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (D : ZeroCenteredData A) {e : Equiv.Perm (Fin n)}
    {U : DefSet (rawMixedSpace (M := M) 0 q) S}
    {T : OrderedStandardContractionProgram (G := G) S (reindexedVFSet D.map.image e) U}
    (V : OrderedStandardContractionLift T) (p : A)
    (hInd : AlgebraicIndependent (vfParameterField S) p.val.1) :
    HasMixedUnitDerivativeAt (D.normalizedOrderedMap V) p := by
  have hDInd := independent_map_of_finiteFibres hc D.bijection
    (Map.finiteFibres_of_injective (D.bijective h00).injective) p hInd
  exact (V.originalMap_generic_unit hv (D.image_properInvariant h00 hc hκ hs hv) (D.bijection p) hDInd).comp
    (D.unit_derivative hv p)

theorem normalizedOrderedMap_unit_derivative_ae
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hn : 0 < n)
    (D : ZeroCenteredData A) {e : Equiv.Perm (Fin n)}
    {U : DefSet (rawMixedSpace (M := M) 0 q) S}
    {T : OrderedStandardContractionProgram (G := G) S (reindexedVFSet D.map.image e) U}
    (V : OrderedStandardContractionLift T) :
    ∃ E : DefSet (rawMixedSpace (M := M) n r) S,E.carrier ⊆ A.carrier ∧
      vfDim (rawRVSpace (M := M) 1) E < n ∧
      ∀ p : A,p.val ∉ E.carrier → HasMixedUnitDerivativeAt (D.normalizedOrderedMap V) p :=
  exists_mixed_unit_derivative_exception hc hs hsmall hn (D.normalizedOrderedMap V)
    (D.normalizedOrderedMap_generic_unit h00 hc hκ hs hv V)

end ZeroCenteredData
end DiamondIntegral.Section6
