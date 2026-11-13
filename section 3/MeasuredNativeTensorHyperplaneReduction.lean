import «section 3».MeasuredNativeRESPartitions
import «section 3».MeasuredHyperplaneTensorReduction
import «section 3».MeasuredPureNativeNormalForm
import «section 3».MeasuredNativeGammaPartitions
import «section 3».GammaGroundBooleanPartitions
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

/-- Exceptional measured native tensors lose one free Gamma coordinate
in an actual positive finite normal form, retaining total degree and weights. -/
theorem gammaGroundMeasuredNativeTensor_finite_hyperplane_normal_form {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (X : GammaGroundRESUnitChart hc B r) (G : GammaGroundGammaPiece hc B (1+n))
    (f : (Fin (1+n) → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hf : FullGammaFunction (integrationGammaBase B) f) (hdegree : r+(1+n) = k)
    (J : Finset (GammaGroundCharacterHyperplane B (1+n)))
    (hcover : ∀ γ ∈ G.carrier, ∃ h ∈ J, γ ∈ h.carrier) :
    ∃ l : List (GammaGroundMeasuredNativeTensorChart hc B k),
      gammaGroundMeasuredRESDirectSumClass X.measured ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
        gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight G f hf) =
        (l.map GammaGroundMeasuredNativeTensorChart.value).sum ∧
          ∀ Z ∈ l, Z.underlying.gammaDegree ≤ n := by
  let e := (Fintype.equivFin {h // h ∈ J}).symm
  let H := fun a : Fin (Fintype.card {h // h ∈ J}) => (e a).val
  let E := fun i => (H i).defSet (hc := hc)
  let Q := gammaGroundBooleanAtom G E
  have hp (b : Fin (Fintype.card {h // h ∈ J}) → Bool) :
      ∃ l : List (GammaGroundMeasuredNativeTensorChart hc B k),
        gammaGroundMeasuredRESDirectSumClass X.measured ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
          gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight (Q b) f hf) =
          (l.map GammaGroundMeasuredNativeTensorChart.value).sum ∧
            ∀ Z ∈ l, Z.underlying.gammaDegree ≤ n := by
    by_cases hne : (Q b).carrier.Nonempty
    · obtain ⟨γ,hγ⟩ := hne
      obtain ⟨h,hh,hγh⟩ := hcover γ hγ.1
      let i := e.symm ⟨h,hh⟩
      have hi : H i = h := congrArg Subtype.val (e.apply_symm_apply ⟨h,hh⟩)
      have hγi : γ ∈ (E i).carrier := by
        change γ ∈ (H i).carrier
        rw [hi]
        exact hγh
      have hsub : (Q b).carrier ⊆ (H i).carrier := by
        intro η hη
        exact (hη.2 i).mpr ((hγ.2 i).mp hγi)
      obtain ⟨F,W,w,hw,he⟩ := gammaGroundMeasuredTensor_character_hyperplane_reduction X.measured (H i) (Q b) ⟨γ,hγ⟩ hsub f hf
      obtain ⟨l,hl,hr⟩ := gammaGroundMeasuredTensor_pure_native_normal_form hκ hs h00 hsmall hγsmall
        (X.measured.product F.resLift) (gammaGroundMeasuredGammaSingleWeight W w hw) (by omega : (r+1)+n = k)
      exact ⟨l,he.trans hl,fun Z hZ => (hr Z hZ).le⟩
    · have he : Q b = GammaGroundDefSet.empty hc B ((volumeGammaSpace hc).power (Fin (1+n))) := by
        apply gammaGroundDefSet_eq_of_carrier_eq
        exact Set.eq_empty_iff_forall_notMem.mpr (fun γ hγ => hne ⟨γ,hγ⟩)
      refine ⟨[],?_,by simp⟩
      rw [he,gammaGroundMeasuredGammaSemiringClass_single_empty,TensorProduct.tmul_zero]
      rfl
  choose l hl hr using hp
  let I := Fin (Fintype.card {h // h ∈ J}) → Bool
  let q := (Fintype.equivFin I).symm
  let parts := List.ofFn (fun a => l (q a))
  refine ⟨parts.flatten,?_,?_⟩
  · have hG := gammaGroundMeasuredGammaSemiringClass_native_finite_partition G Q
      (gammaGroundBooleanAtom_disjoint G E) (gammaGroundBooleanAtom_cover G E) f hf
    rw [hG,TensorProduct.tmul_sum]
    calc
      _ = ∑ b : I, ((l b).map GammaGroundMeasuredNativeTensorChart.value).sum := Finset.sum_congr rfl (fun b _ => hl b)
      _ = ∑ a, ((l (q a)).map GammaGroundMeasuredNativeTensorChart.value).sum :=
        (Equiv.sum_comp q (fun b => ((l b).map GammaGroundMeasuredNativeTensorChart.value).sum)).symm
      _ = _ := by simp only [parts,List.map_flatten,List.sum_flatten,List.map_ofFn,List.sum_ofFn,Function.comp_def]
  · intro Z hZ
    obtain ⟨p,hp,hZ⟩ := List.mem_flatten.mp hZ
    obtain ⟨a,rfl⟩ := List.mem_ofFn.mp hp
    exact hr (q a) Z hZ
end DiamondIntegral.Section3
