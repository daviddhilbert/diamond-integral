import «section 6».AllDimensionalMeasuredOrderedPrograms
import «section 6».PermutedMeasuredOrderedForms
import «section 6».NormalizedOrderedContractionLifts

/-! Measured standard contractions in every positive VF dimension, for
arbitrary proper sources and every coordinate order. The actual permitted
normalization, exact source form transport and full measure identity are
retained over the original base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

structure NormalizedMeasuredContraction
    (A : DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) (e : Equiv.Perm (Fin (n+1))) where
  normalization : ZeroCenteredData A
  preparedForm : Map (reindexedVFSet normalization.map.image e) (DefSet.univ (rawGammaPresentation (M := M)) S)
  transport : ∀ p : A,(preparedForm (vfRelabeling normalization.map.image e (normalization.bijection p))).val=(ω p).val
  preparedContraction : MeasuredOrderedContraction (G := G) (reindexedVFSet normalization.map.image e) preparedForm

namespace NormalizedMeasuredContraction
variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}
variable {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)} {e : Equiv.Perm (Fin (n+1))}

def target (F : NormalizedMeasuredContraction (G := G) A ω e) := F.preparedContraction.lift.originalTarget

def map (F : NormalizedMeasuredContraction (G := G) A ω e) : Map A F.target :=
  F.normalization.normalizedOrderedMap F.preparedContraction.lift

def form (F : NormalizedMeasuredContraction (G := G) A ω e) :=
  F.preparedContraction.data.originalTargetForm F.preparedContraction.lift

theorem form_transport (F : NormalizedMeasuredContraction (G := G) A ω e) (p : A) :
    (F.form (F.map p)).val=(ω p).val :=
  (F.preparedContraction.data.originalTargetForm_transport F.preparedContraction.lift (F.normalization.bijection p)).trans
    (F.transport p)

theorem form_same_tags (F : NormalizedMeasuredContraction (G := G) A ω e)
    (p z : F.target) (hTags : p.val.2=z.val.2) : F.form p=F.form z :=
  F.preparedContraction.data.originalTargetForm_same_tags F.preparedContraction.lift p z hTags

theorem homeomorphism
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (F : NormalizedMeasuredContraction (G := G) A ω e) : ProperCovariantHomeomorphism F.map :=
  F.normalization.normalizedOrderedMap_homeomorphism h00 hc linear hκ hs hv hsmall hΓ F.preparedContraction.lift

theorem measure_identity_ae
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (F : NormalizedMeasuredContraction (G := G) A ω e) :
    ∃ E : DefSet (rawMixedSpace (M := M) (n+1) r) S,E.carrier ⊆ A.carrier ∧
      vfDim (rawRVSpace (M := M) 1) E < n+1 ∧ ∀ p : A,p.val ∉ E.carrier →
        ∃ J,HasMixedVFJacobianAt F.map p J ∧ vfValue J=(gammaMapValue ω p/gammaMapValue F.form (F.map p)).val := by
  obtain ⟨E,hEA,hDim,hUnit⟩ := F.normalization.normalizedOrderedMap_unit_derivative_ae
    h00 hc hκ hs hv hsmall (Nat.zero_lt_succ n) F.preparedContraction.lift
  refine ⟨E,hEA,hDim,fun p hp => ⟨1,(hUnit p hp).partialJacobian,?_⟩⟩
  have hValues : gammaMapValue F.form (F.map p)=gammaMapValue ω p := F.form_transport p
  rw [hValues,div_self']
  exact (valueHom_eq_value (1 : VF M)).symm.trans
    ((map_one Values.vfValueHom).trans Values.gamma_val_one.symm)

end NormalizedMeasuredContraction

theorem measured_contraction_any_order
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) (n+1) r) S) (hA : ProperInvariant S A.carrier)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hLevels : ∀ u γ,IsOpen {a : Fin (n+1) → VF M | (a,u) ∈ A.carrier ∧ gammaFormExtension ω (a,u)=γ})
    (e : Equiv.Perm (Fin (n+1))) : Nonempty (NormalizedMeasuredContraction (G := G) A ω e) := by
  obtain ⟨D⟩ := exists_zeroCentered_data h00 hc linear hκ hs hv V S hsmall hΓ hV hVS hSV hnt A hA
  let d := D.bijection
  have hd : SpecialCovariantChain (G := G) A D.map.image d := .zeroCentered A D
  let η := ω.comp (d.inverse (D.bijective h00))
  have hTransportD (p : A) : (η (d p)).val=(ω p).val := by
    change (ω (d.inverse (D.bijective h00) (d p))).val=_
    rw [Map.inverse_apply]
  have hLevelsD := hd.exact_gamma_levels_open h00 hc linear hκ hs hv hsmall hΓ ω hLevels η hTransportD
  let E := vfRelabeling D.map.image e
  let θ := η.comp (E.inverse (vfRelabeling_bijective D.map.image e))
  have hLevelsE := vfRelabeling_gamma_levels_open h00 hc linear hκ hs hv hsmall hΓ D.map.image e
    (D.image_properInvariant h00 hc hκ hs hv) η hLevelsD
  obtain ⟨F⟩ := measured_ordered_contraction_all_dimensions h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt
    (reindexedVFSet D.map.image e) (reindexedVFSet_properInvariant D.map.image e (D.image_properInvariant h00 hc hκ hs hv))
    (reindexedVFSet_doublyBounded D.map.image e D.image_vfDoublyBounded) θ hLevelsE
  refine ⟨⟨D,θ,?_,F⟩⟩
  intro p
  change (η (E.inverse (vfRelabeling_bijective D.map.image e) (E (d p)))).val=(ω p).val
  rw [Map.inverse_apply]
  exact hTransportD p

end DiamondIntegral.Section6
