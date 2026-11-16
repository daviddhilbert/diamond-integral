import «section 6».BinaryMeasuredOrderedPrograms

/-! An actual measured ordered contraction includes its full ordered
lift. The descended form is exactly transported on every point, and
the VF measure identity holds on the approved common good locus. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

structure MeasuredOrderedContraction
    (A : DefSet (rawMixedSpace (M := M) n r) S)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) where
  data : MeasuredOrderedProgram (G := G) A ω
  lift : OrderedStandardContractionLift data.program

namespace MeasuredOrderedContraction
variable {A : DefSet (rawMixedSpace (M := M) n r) S}
variable {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)}

def form (F : MeasuredOrderedContraction (G := G) A ω) := F.data.targetForm F.lift

theorem form_transport (F : MeasuredOrderedContraction (G := G) A ω) (p : A) :
    (F.form (F.lift.map p)).val=(ω p).val := F.data.targetForm_transport F.lift p

theorem form_same_tags (F : MeasuredOrderedContraction (G := G) A ω)
    (p z : F.lift.target) (hTags : p.val.2=z.val.2) : F.form p=F.form z :=
  F.data.targetForm_same_tags F.lift p z hTags

theorem measure_identity_ae
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ) (hn : 0 < n)
    (F : MeasuredOrderedContraction (G := G) A ω) :
    ∃ E : DefSet (rawMixedSpace (M := M) n r) S,E.carrier ⊆ A.carrier ∧
      vfDim (rawRVSpace (M := M) 1) E < n ∧ ∀ p : A,p.val ∉ E.carrier →
        ∃ J,HasMixedVFJacobianAt F.lift.map p J ∧
          vfValue J=(gammaMapValue ω p/gammaMapValue F.form (F.lift.map p)).val := by
  obtain ⟨E,hEA,hDim,hUnit⟩ := F.lift.unit_derivative_ae hc hs hsmall hn
  refine ⟨E,hEA,hDim,fun p hp => ⟨1,(hUnit p hp).partialJacobian,?_⟩⟩
  have hValues : gammaMapValue F.form (F.lift.map p)=gammaMapValue ω p := F.form_transport p
  rw [hValues,div_self']
  exact (valueHom_eq_value (1 : VF M)).symm.trans
    ((map_one Values.vfValueHom).trans Values.gamma_val_one.symm)

def headStartObject
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (F : MeasuredOrderedContraction (G := G) A ω) (k : ℕ) (π : Fin k → Fin r)
    (hFin : ∀ a : Fin n → VF M,∀ t : Fin k → RVInfinity M,
      {u : Fin r → RVInfinity M | (a,u) ∈ A.carrier ∧ u ∘ π=t}.Finite) : MeasuredRVObject (M := M) S (n+k) :=
  F.lift.headStartMeasuredObject hc h00 hκ hs hsmall k π hFin F.form F.form_same_tags

end MeasuredOrderedContraction

theorem binary_measured_ordered_contraction
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 2 r) S) (hA : ProperInvariant S A.carrier)
    (hAD : VFDoublyBounded A.carrier)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hLevels : ∀ u γ,IsOpen {a : Fin 2 → VF M | (a,u) ∈ A.carrier ∧ gammaFormExtension ω (a,u)=γ}) :
    Nonempty (MeasuredOrderedContraction (G := G) A ω) := by
  obtain ⟨F⟩ := binary_measured_ordered_program h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt A hA hAD ω hLevels
  obtain ⟨L⟩ := exists_ordered_standard_contraction_lift h00 hc linear hκ hs hv hsmall hΓ F.program hA
  exact ⟨⟨F,L⟩⟩

end DiamondIntegral.Section6
