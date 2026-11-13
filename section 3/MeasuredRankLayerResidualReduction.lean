import «section 3».MeasuredRankLayerResidualAtlas
import «section 3».MeasuredNativeTensorHyperplaneReduction
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {k : ℕ}
variable {ι : Type} [Fintype ι]
namespace GammaGroundMeasuredTensorResidual
/-- Once the unmatched maximal-rank Gamma factors are covered by the
finite exceptional hyperplanes, the complete residual value has a
strictly smaller-rank homogeneous native normal form. -/
theorem lower_normal_form {n : ℕ}
    (L : GammaGroundMeasuredTensorRankLayer hc B k (1+n))
    (E : GammaGroundTensorRankLayerMatchedFamily L.unmeasured ι)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (Q : Fin L.topCount → Finset (GammaGroundCharacterHyperplane B (1+n)))
    (hcover : ∀ j (x : gammaGroundNativeProductDomain (L.residue j) (L.gamma j)),
      (L.unmeasured.topMap j x).val ∈ E.union.carrier ∨
        ∃ h ∈ Q j, rvUnitTupleValues x.val.1 ∈ h.carrier) :
    ∃ l : List (GammaGroundMeasuredNativeTensorChart hc B k),
      (∑ c : E.ResidualIndex, (chart L E c).value) =
        (l.map GammaGroundMeasuredNativeTensorChart.value).sum ∧
          ∀ Z ∈ l, Z.underlying.gammaDegree ≤ n := by
  have hnf (c : E.ResidualIndex) : ∃ l : List (GammaGroundMeasuredNativeTensorChart hc B k),
      (chart L E c).value = (l.map GammaGroundMeasuredNativeTensorChart.value).sum ∧
        ∀ Z ∈ l, Z.underlying.gammaDegree ≤ n := by
    rcases c with ⟨j,c⟩ | j
    · let A := E.remainderBox ⟨j,c⟩
      have hγ := gammaGroundTensorParentRemainder_gamma_cover L.residue L.gamma L.unmeasured.topMap
        L.unmeasured.topMap_injective L.unmeasured.topMap_disjoint E.parent E.box Q hcover j c
      exact gammaGroundMeasuredNativeTensor_finite_hyperplane_normal_form hκ hs h00 hsmall hγsmall
        ((L.residue j).restrict A.residue A.residue_subset) A.gamma (L.weight j) (L.weight_definable j)
        (Nat.sub_add_cancel L.within_degree) (Q j) hγ
    · refine ⟨[L.lowerChart j],by simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]; rfl,?_⟩
      intro Z hZ
      have he : Z = L.lowerChart j := List.mem_singleton.mp hZ
      subst Z
      have hr := L.unmeasured.lower_rank_at j
      change (L.lower.get j).gammaDegree ≤ n
      change (L.lower.get j).gammaDegree < 1+n at hr
      omega
  choose l hl hr using hnf
  let q := (Fintype.equivFin E.ResidualIndex).symm
  let parts := List.ofFn (fun a => l (q a))
  refine ⟨parts.flatten,?_,?_⟩
  · calc
      _ = ∑ c : E.ResidualIndex, ((l c).map GammaGroundMeasuredNativeTensorChart.value).sum :=
        Finset.sum_congr rfl (fun c _ => hl c)
      _ = ∑ a, ((l (q a)).map GammaGroundMeasuredNativeTensorChart.value).sum :=
        (Equiv.sum_comp q (fun c => ((l c).map GammaGroundMeasuredNativeTensorChart.value).sum)).symm
      _ = _ := by simp only [parts,List.map_flatten,List.sum_flatten,List.map_ofFn,List.sum_ofFn,Function.comp_def]
  · intro Z hZ
    obtain ⟨p,hp,hZ⟩ := List.mem_flatten.mp hZ
    obtain ⟨a,rfl⟩ := List.mem_ofFn.mp hp
    exact hr (q a) Z hZ
end GammaGroundMeasuredTensorResidual
end DiamondIntegral.Section3
