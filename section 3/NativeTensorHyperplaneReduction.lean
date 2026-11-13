import «section 3».FiniteHyperplaneTensorReduction
import «section 3».NativeTensorCharts
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open scoped TensorProduct
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {k r n : ℕ}

/-- A positive native product lying in finitely many proper Gamma
hyperplanes has a finite normal form of strictly smaller free arity,
with its original total degree retained. -/
theorem gammaGroundNativeTensor_finite_hyperplane_normal_form
    (h00 : M ⊨ Axioms.ACVF00) (X : GammaGroundRESUnitChart hc B r)
    (G : GammaGroundGammaPiece hc B (1+n)) (hdegree : r+(1+n) = k)
    (J : Finset (GammaGroundCharacterHyperplane B (1+n)))
    (hcover : ∀ γ ∈ G.carrier, ∃ h ∈ J, γ ∈ h.carrier) :
    ∃ l : List (GammaGroundNativeTensorChart hc B k),
      gammaGroundRESDirectSumClass X.object ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
        gammaGroundGammaSemiringClass (GammaGroundGammaObject.single G) =
        (l.map GammaGroundNativeTensorChart.value).sum ∧
          ∀ Z ∈ l, Z.gammaDegree ≤ n := by
  let e := (Fintype.equivFin {h // h ∈ J}).symm
  let H := fun a : Fin (Fintype.card {h // h ∈ J}) => (e a).val
  have hcovFin : ∀ γ ∈ G.carrier, ∃ a, γ ∈ (H a).carrier := by
    intro γ hγ
    obtain ⟨h,hh,hγh⟩ := hcover γ hγ
    let s : {h // h ∈ J} := ⟨h,hh⟩
    refine ⟨e.symm s,?_⟩
    simpa only [H,e.apply_symm_apply] using hγh
  obtain ⟨Y,W,hYW⟩ := gammaGroundUnmeasuredTensor_finite_hyperplane_reduction X.object G H hcovFin
  let I := Fin (Fintype.card {h // h ∈ J}) → Bool
  let Z : I → GammaGroundNativeTensorChart hc B k := fun b =>
    ⟨r+1,n,by omega,gammaGroundRESUnitChart h00 (Y b),W b⟩
  let q := (Fintype.equivFin I).symm
  refine ⟨List.ofFn (fun a => Z (q a)),?_,?_⟩
  · rw [List.map_ofFn,List.sum_ofFn]
    exact hYW.trans (Equiv.sum_comp q (fun b => (Z b).value)).symm
  · intro A hA
    obtain ⟨a,rfl⟩ := List.mem_ofFn.mp hA
    exact Nat.le_refl n
end DiamondIntegral.Section3
