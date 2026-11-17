import «section 3».GammaHeadMeasuredFibres
import «section 3».GammaHeadRetainedForms
import IntegrationSection6.GammaPermutedFibrePresentations
import «section 3».GammaGroundVFPermutationJacobians

/-! Actual VF coordinate permutations are full measured Gamma maps
for every retained form. Their permutation sign has Gamma value one. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section5 IntegrationInACVF.Section6
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable {n a : ℕ}
variable (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) n a)
variable (hA : GammaSetDefinable B (carrier A))
variable (hfin : ∀ x : Fin n → VF (M := M), {r | (x,r) ∈ carrier A}.Finite)
variable (Q : GammaGroundDefSet hc B (rawRVSpace (M := M) a))
variable (hQ : ∀ p : A, p.val.2 ∈ Q.carrier) (ω : GammaGroundVolumeForm hc B Q)

include hBC hv in
def gammaNativeFullMeasuredPermutation (σ : Equiv.Perm (Fin n)) :
    GammaFullMeasuredBijection
      (gammaPointMeasuredData A hA hfin (gammaPointRetainedForm A hA Q id hQ ω))
      (gammaPointMeasuredData (vfPermutationImage A σ) (gamma_vfPermutationImage A hA σ)
        (vfPermutation_finite_rv_fibres A σ hfin)
        (gammaPointRetainedForm (vfPermutationImage A σ) (gamma_vfPermutationImage A hA σ) Q id
          (fun p => by
            obtain ⟨q,hq⟩ := (vfPermutationBijection_bijective A σ).surjective p
            exact (congrArg Prod.snd (congrArg Subtype.val hq)) ▸ hQ q) ω)) := by
  let f := Section5.nativeGammaPointBijection (hc := hc) hA (gamma_vfPermutationImage A hA σ)
    (⟨Equiv.ofBijective (vfPermutationBijection A σ) (vfPermutationBijection_bijective A σ),
      gamma_vfPermutation_graph A hA σ⟩ : GammaIso B (carrier A) (carrier (vfPermutationImage A σ)))
  refine ⟨f,?_⟩
  intro p hp
  refine ⟨(Equiv.Perm.sign σ : Section2.VF M),?_,?_⟩
  · exact gammaGroundVFPermutation_jacobian C.uncountable.le C.saturated
      ((Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small) hv f.map σ (fun q => by
        rw [Section5.nativeGammaPointBijection_apply]; rfl) p hp
  · rw [gammaVFPermutationSign_value,mul_one]
    change (cast (gammaCarrier hc) (ω ⟨p.val.2,hQ ⟨p.val,p.property⟩⟩).val).val = _
    apply congrArg (fun q : GammaGroundDefSet.univ hc B (volumeGammaSpace hc) =>
      (cast (gammaCarrier hc) q.val).val)
    apply congrArg ω
    apply Subtype.ext
    change p.val.2 = (f.map p).val.2
    rw [Section5.nativeGammaPointBijection_apply]
    rfl

theorem gammaNativeFullMeasuredPermutation_VF (σ : Equiv.Perm (Fin n))
    (p : Section5.nativeGammaPointDomain (hc := hc) (carrier A) hA) :
    ((gammaNativeFullMeasuredPermutation C hBC hv A hA hfin Q hQ ω σ).map.map p).val.1 = p.val.1 ∘ σ := by
  change ((Section5.nativeGammaPointBijection (hc := hc) hA
    (gamma_vfPermutationImage A hA σ) _).map p).val.1 = _
  rw [Section5.nativeGammaPointBijection_apply]
  rfl

end DiamondIntegral.Section3
