import «section 5».NativeWeakVFLiftSchemata
import «section 5».NativeVFLiftRVPreparation
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6
open DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {p q n r m s : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}

theorem NativeVFLiftEqualitySchema.rv_values_descend_weak
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) {kind : EulerKind}
    {D : Set (Fin (p+(n+r)) → M)} {E : Set (Fin (p+(m+s)) → M)}
    (W : NativeVFLiftEqualitySchema (B := B) (sp := sp) hc kind D E)
    (R : GammaParameterRecode B p q sp sq) (z : Fin p → M) (t : Fin q → M)
    (hz : ∀ i, sortEval (sp i) (z i)) (ht : ∀ i, sortEval (sq i) (t i))
    (hv : W.ValidWeak hc z) (ha : W.RVAgreement R z t) :
    (nativeFiniteRVSchemaRecode R W.leftRV).valid t ∧
      (nativeFiniteRVSchemaRecode R W.rightRV).valid t ∧
        nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ kind (R.domain (finiteRVSchemaDomain W.leftRV)) t =
          nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ kind (R.domain (finiteRVSchemaDomain W.rightRV)) t := by
  refine ⟨(finiteRVSchema_valid_recode_iff R W.leftRV z t hz ht ha.2.1 ha.2.2.2.1).mp hv.1,
    (finiteRVSchema_valid_recode_iff R W.rightRV z t hz ht ha.2.2.1 ha.2.2.2.2).mp hv.2.1,?_⟩
  exact (W.evaluation.recode R).native_equality hc h00 linear hκ hs hr hγ hΓ t
    ((W.evaluation.recode_valid_iff R z t hz ht ha.1).mp hv.2.2.2.2)


end DiamondIntegral.Section5
