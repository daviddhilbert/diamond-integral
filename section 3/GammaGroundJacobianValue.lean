import «section 3».GammaGroundJacobianGraph
import «section 3».GammaGroundConstants

/-! A total determinant function over the original Gamma ground. The
value outside the full derivative locus is zero; no coefficients or
representatives are added to the base. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}
variable {n r s : ℕ}
variable {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r)}
variable {D : GammaGroundDefSet hc B (rawMixedSpace (M := M) n s)}

def gammaGroundJacobianValue (f : GammaGroundMap A D) (p : A) : VFType (M := M) :=
  if h : ∃ L, HasMixedVFDerivativeAt f p L then
    (LinearMap.toMatrix' (Classical.choose h)).det else 0

theorem gammaGroundJacobianValue_of_derivative (f : GammaGroundMap A D) (p : A)
    (L : (Fin n → VFType (M := M)) →ₗ[VFType (M := M)] (Fin n → VFType (M := M)))
    (hL : HasMixedVFDerivativeAt f p L) :
    gammaGroundJacobianValue f p = (LinearMap.toMatrix' L).det := by
  rw [gammaGroundJacobianValue, dite_eq_left ⟨L,hL⟩]
  obtain ⟨F,hF,hDF⟩ := Classical.choose_spec (show ∃ K, HasMixedVFDerivativeAt f p K from ⟨L,hL⟩)
  obtain ⟨H,hH,hDH⟩ := hL
  exact HasMixedVFJacobianAt.unique ⟨F,hF,hDF.hasJacobianAt⟩ ⟨H,hH,hDH.hasJacobianAt⟩

def gammaGroundJacobianValueMap (hn : 0 < n) (f : GammaGroundMap A D) :
    GammaGroundMap A (GammaGroundDefSet.univ hc B (rawVFSpace (M := M) 1)) where
  toFun p := ⟨fun _ => gammaGroundJacobianValue f p, Set.mem_univ _⟩
  graph_definable := by
    let P := rawMixedSpace (M := M) n r
    let Q := rawVFSpace (M := M) 1
    let Z : GammaGroundMap A (GammaGroundDefSet.univ hc B Q) :=
      GammaGroundMap.ofGlobal A _ (by
        exact Map.ofCodes (DefSet.univ P B.real) (fun _ _ => (0 : VFType (M := M)))
          (fun _ _ => iVFZero)
          (fun _ => (SpecialTransformations.DefinableConstants.constant (SpecialTransformations.DefinableConstants.function_symbol
            (L := LRV) Fn.vfZero Fin.elim0 (fun i => i.elim0))).mono (Set.empty_subset _))
          (fun _ => ⟨fun _ => 0,rfl⟩)
          (fun _ => vfValues_injective (vfValues_decode _))) (fun _ => Set.mem_univ _)
    have hEx := (gammaGroundDifferentiabilityLocus hn f).definable.preimage
      (universalProductFst P Q B.real)
    apply ((gammaGroundFullJacobianRelation_definable hn f).union
      (Z.graph_definable.inter hEx.compl)).congr
    intro z
    constructor
    · rintro (⟨p,hp,L,hL,hdet⟩ | ⟨⟨p,hp,hz⟩,hnot⟩)
      · refine ⟨p,hp,?_⟩
        funext i
        have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
        subst i
        exact (gammaGroundJacobianValue_of_derivative f p L hL).trans hdet
      · refine ⟨p,hp,?_⟩
        have hnL : ¬ ∃ L, HasMixedVFDerivativeAt f p L := by
          rintro ⟨L,hL⟩
          exact hnot ((mem_gammaGroundDifferentiabilityLocus hn f z.1).mpr ⟨p,hp,L,hL⟩)
        change (fun _ => gammaGroundJacobianValue f p) = z.2
        rw [gammaGroundJacobianValue,dite_eq_right hnL]
        exact hz
    · rintro ⟨p,hp,hz⟩
      by_cases h : ∃ L, HasMixedVFDerivativeAt f p L
      · obtain ⟨L,hL⟩ := h
        left
        refine ⟨p,hp,L,hL,?_⟩
        exact (gammaGroundJacobianValue_of_derivative f p L hL).symm.trans (congrFun hz 0)
      · right
        refine ⟨⟨p,hp,?_⟩,?_⟩
        · change (fun _ => (0 : VFType (M := M))) = z.2
          simpa only [gammaGroundJacobianValue,dite_eq_right h] using hz
        · intro hm
          obtain ⟨q,hq,L,hL⟩ := (mem_gammaGroundDifferentiabilityLocus hn f z.1).mp hm
          have he : q = p := Subtype.ext (hq.trans hp.symm)
          exact h ⟨L,he ▸ hL⟩

theorem gammaGroundJacobianValueMap_of_derivative (hn : 0 < n) (f : GammaGroundMap A D)
    (p : A) (L : (Fin n → VFType (M := M)) →ₗ[VFType (M := M)] (Fin n → VFType (M := M)))
    (hL : HasMixedVFDerivativeAt f p L) :
    (gammaGroundJacobianValueMap hn f p).val 0 = (LinearMap.toMatrix' L).det :=
  gammaGroundJacobianValue_of_derivative f p L hL

end DiamondIntegral.Section3
