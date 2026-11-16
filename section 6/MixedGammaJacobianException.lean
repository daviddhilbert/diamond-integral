import «section 6».ScalarGammaValues
import Section9.MixedJacobianValue
import Section9.MixedDifferentiationAE

/-! A full derivative with a prescribed Gamma determinant is an actual
original-base definable condition. A generic identity therefore gives
one VF-small exception over that same base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r s : ℕ} {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}

theorem exists_mixedGammaJacobian_good_locus (hn : 0 < n) (f : Map A B)
    (ν : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) :
    ∃ H : DefSet (rawMixedSpace (M := M) n r) S, ∀ p : A,
      p.val ∈ H.carrier ↔ ∃ L, HasMixedVFDerivativeAt f p L ∧
        vfValue (LinearMap.toMatrix' L).det = (gammaMapValue ν p).val := by
  obtain ⟨j,hj⟩ := exists_totalMixedJacobianMap f
  let P := rawMixedSpace (M := M) n r
  let Q := rawGammaPresentation (M := M)
  let v := (scalarGammaValueMap S).comp j
  let h := v.pair ν
  have hDiag : (Q.prod Q).Definable S {z | z.1 = z.2} :=
    (Q.definable_prod_iff Q S Eq).mpr (Q.diagonal_definable.mono (Set.empty_subset S))
  let C := {x | ∃ p : A, p.val = x ∧ (h p).val.1 = (h p).val.2}
  have hC : P.Definable S C := h.definable_preimage hDiag
  let D := {x | ∃ p : A, p.val = x ∧ ∃ L, HasMixedVFDerivativeAt f p L}
  have hD : P.Definable S D := mixedDifferentiabilityLocus_definable hn f
  let N := {p : Mixed M n r | scalarCodeExtension j (mixedValues p) ≠ iVFZero}
  have hz : S.DefinableFun LRV (fun _ : Fin n ⊕ Fin r → M => iVFZero) :=
    (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.vfZero)).comp
      (show S.DefinableMap LRV (fun _ : Fin n ⊕ Fin r → M => Fin.elim0) from fun i => i.elim0)
  have hN : P.Definable S N := mixedValues_preimage_definable
    {z | scalarCodeExtension j z ≠ iVFZero} (((scalarCodeExtension_definable j).ofPred_eq hz).compl)
  refine ⟨⟨D ∩ C ∩ N,(hD.inter P hC).inter P hN⟩,fun p => ⟨?_,?_⟩⟩
  · rintro ⟨⟨⟨p₁,hp₁,L,hL⟩,⟨p₂,hp₂,he⟩⟩,hNZ⟩
    have he₁ : p₁ = p := Subtype.ext hp₁
    have he₂ : p₂ = p := Subtype.ext hp₂
    subst p₁
    subst p₂
    have hjNZ : (j p).val 0 ≠ 0 := by
      intro hj0
      apply hNZ
      rw [scalarCodeExtension_at j p,hj0]
      rfl
    have hVal := scalarGammaValueMap_nonzero S (j p).val hjNZ
    change ((v p).val : Gamma M).val = vfValue ((j p).val 0) at hVal
    change (v p).val = (ν p).val at he
    refine ⟨L,hL,?_⟩
    rw [← hj p L hL]
    exact hVal.symm.trans (congrArg (fun γ : Gamma M => γ.val) he)
  · rintro ⟨L,hL,hVal⟩
    have hdet : (LinearMap.toMatrix' L).det ≠ 0 := by
      intro hzero
      have hInf := (vfValue_eq_infinity_iff _).mpr hzero
      exact (gammaMapValue ν p).property (hVal.symm.trans hInf)
    have hjNZ : (j p).val 0 ≠ 0 := by rwa [hj p L hL]
    have hValue := scalarGammaValueMap_nonzero S (j p).val hjNZ
    have hEq : (v p).val = (ν p).val := by
      apply Subtype.ext
      change ((v p).val : Gamma M).val = ((ν p).val : Gamma M).val
      calc
        _ = vfValue ((j p).val 0) := hValue
        _ = vfValue (LinearMap.toMatrix' L).det := congrArg vfValue (hj p L hL)
        _ = _ := hVal
    refine ⟨⟨⟨p,rfl,L,hL⟩,⟨p,rfl,hEq⟩⟩,?_⟩
    change scalarCodeExtension j (mixedValues p.val) ≠ iVFZero
    rw [scalarCodeExtension_at j p]
    intro hz0
    exact hjNZ (Subtype.ext hz0)

theorem exists_mixedGammaJacobian_exception
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ) (hn : 0 < n)
    (f : Map A B) (ν : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hGeneric : ∀ p : A, AlgebraicIndependent (vfParameterField S) p.val.1 →
      ∃ L, HasMixedVFDerivativeAt f p L ∧ vfValue (LinearMap.toMatrix' L).det = (gammaMapValue ν p).val) :
    ∃ E : DefSet (rawMixedSpace (M := M) n r) S, E.carrier ⊆ A.carrier ∧
      vfDim (rawRVSpace (M := M) 1) E < n ∧
      ∀ p : A, p.val ∉ E.carrier → ∃ L, HasMixedVFDerivativeAt f p L ∧
        vfValue (LinearMap.toMatrix' L).det = (gammaMapValue ν p).val := by
  obtain ⟨H,hH⟩ := exists_mixedGammaJacobian_good_locus hn f ν
  let E : DefSet (rawMixedSpace (M := M) n r) S := ⟨A.carrier \ H.carrier,A.definable.sdiff _ H.definable⟩
  refine ⟨E,Set.diff_subset,?_,?_⟩
  · apply mixed_vfDim_lt_of_no_independent hc hs hsmall _ (rawRVSpace_rvCoded 1) hn
    intro p hp
    exact p.property.2 ((hH ⟨p.val,p.property.1⟩).mpr (hGeneric _ hp))
  · intro p hp
    apply (hH p).mp
    by_contra hnH
    exact hp ⟨p.property,hnH⟩

end DiamondIntegral.Section6
