import «section 6».VFRelabelingHomeomorphisms
import «section 6».OrderedContractionLiftProperties

/-! Transport an actual ordered program back to the original VF
coordinates. Its order is e(last), ..., e(0), and its full lift has
unit total determinant after the two coordinate relabelings cancel. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r q : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {e : Equiv.Perm (Fin n)}
variable {U : DefSet (rawMixedSpace (M := M) 0 q) S}
variable {T : OrderedStandardContractionProgram (G := G) S (reindexedVFSet A e) U}
namespace OrderedStandardContractionLift

def originalTarget (V : OrderedStandardContractionLift T) := reindexedVFSet V.target e.symm

def originalMap (V : OrderedStandardContractionLift T) : Map A V.originalTarget :=
  (vfRelabeling V.target e.symm).comp (V.map.comp (vfRelabeling A e))

def originalContraction (V : OrderedStandardContractionLift T) : Map A U :=
  T.toMap.comp (vfRelabeling A e)

theorem originalMap_value (V : OrderedStandardContractionLift T) (p : A) :
    (V.originalMap p).val=((V.map (vfRelabeling A e p)).val.1 ∘ e.symm,(V.map (vfRelabeling A e p)).val.2) := rfl

theorem originalMap_labels (V : OrderedStandardContractionLift T) (p : A) :
    (V.originalMap p).val.2=(V.originalContraction p).val.2 := V.labels _

theorem originalTarget_proper (V : OrderedStandardContractionLift T) : ProperInvariant S V.originalTarget.carrier :=
  reindexedVFSet_properInvariant V.target e.symm V.proper

theorem originalTarget_doublyBounded (V : OrderedStandardContractionLift T) : VFDoublyBounded V.originalTarget.carrier :=
  reindexedVFSet_doublyBounded V.target e.symm V.doublyBounded

theorem originalTarget_pullback (V : OrderedStandardContractionLift T) : IsRVPullback V.originalTarget.carrier :=
  reindexedVFSet_rvPullback V.target e.symm V.pullback

theorem originalTarget_recover (V : OrderedStandardContractionLift T) (p : Mixed M n q) :
    p ∈ V.originalTarget.carrier ↔ (Fin.elim0,p.2) ∈ U.carrier ∧
      ∀ i,rv M (p.1 i)=p.2 (T.volumeIndex (e.symm i)) := by
  rw [originalTarget,mem_reindexedVFSet]
  change (p.1 ∘ e,p.2) ∈ V.target.carrier ↔ _
  rw [V.recover]
  constructor
  · rintro ⟨h,hVolume⟩
    refine ⟨h,fun i => ?_⟩
    simpa only [Function.comp_apply,Equiv.apply_symm_apply] using hVolume (e.symm i)
  · rintro ⟨h,hVolume⟩
    refine ⟨h,fun i => ?_⟩
    simpa only [Function.comp_apply,Equiv.symm_apply_apply] using hVolume (e i)

theorem originalMap_homeomorphism
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hA : ProperInvariant S A.carrier) (V : OrderedStandardContractionLift T) :
    ProperCovariantHomeomorphism V.originalMap :=
  lemma_6_9 h00 hc linear hκ hs hv hsmall hΓ
    (lemma_6_9 h00 hc linear hκ hs hv hsmall hΓ
      (vfRelabeling_homeomorphism h00 hc linear hκ hs hv hsmall hΓ A e hA) V.home)
    (vfRelabeling_homeomorphism h00 hc linear hκ hs hv hsmall hΓ V.target e.symm V.proper)

theorem originalMap_generic_unit
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hA : ProperInvariant S A.carrier) (V : OrderedStandardContractionLift T)
    (p : A) (hInd : AlgebraicIndependent (vfParameterField S) p.val.1) :
    HasMixedUnitDerivativeAt V.originalMap p := by
  let E := vfRelabeling A e
  let F := vfRelabeling V.target e.symm
  have hE := vfRelabeling_derivative hv A e hA p
  obtain ⟨L,hL,hDet⟩ := V.genericUnit (E p) (hInd.comp e e.injective)
  have hF := vfRelabeling_derivative hv V.target e.symm V.proper (V.map (E p))
  refine ⟨(vfReindexLinear e.symm).comp (L.comp (vfReindexLinear e)),
    mixedDerivative_comp (V.map.comp E) F p (mixedDerivative_comp E V.map p hE hL) hF,?_⟩
  rw [LinearMap.toMatrix'_comp,Matrix.det_mul,LinearMap.toMatrix'_comp,Matrix.det_mul,hDet,one_mul]
  have h := congrArg (fun D => (LinearMap.toMatrix' D).det) (vfReindexLinear_symm_comp (M := M) e)
  simpa only [LinearMap.toMatrix'_comp,Matrix.det_mul,LinearMap.toMatrix'_id,Matrix.det_one] using h

theorem originalMap_unit_derivative_ae
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hn : 0 < n) (hA : ProperInvariant S A.carrier) (V : OrderedStandardContractionLift T) :
    ∃ E : DefSet (rawMixedSpace (M := M) n r) S,E.carrier ⊆ A.carrier ∧
      vfDim (rawRVSpace (M := M) 1) E < n ∧ ∀ p : A,p.val ∉ E.carrier → HasMixedUnitDerivativeAt V.originalMap p :=
  exists_mixed_unit_derivative_exception hc hs hsmall hn V.originalMap (V.originalMap_generic_unit hv hA)

end OrderedStandardContractionLift
end DiamondIntegral.Section6
