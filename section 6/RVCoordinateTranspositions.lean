import «section 6».RVCoordinateArithmeticObjects
import «section 6».FiniteRVIsomorphisms
import Section4.RVReindexing

/-! Coordinate transpositions are composites of actual one-coordinate
operations. This construction retains finite volume at every step and
uses no choice of labels or enlargement of the parameter base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

theorem rv_coordinate_swap_arithmetic (t : Fin n → RVInfinity M) (i j : Fin n)
    (hij : i ≠ j) (hi : t i ≠ 0) (hj : t j ≠ 0) :
    let a := Function.update t i (t i * t j)
    let b := Function.update a j (a i / a j)
    Function.update b i (b i / b j) = t ∘ Equiv.swap i j := by
  dsimp only
  funext k
  by_cases hki : k = i
  · subst k
    simp only [Function.update_self,Function.update_of_ne hij,
      Function.update_of_ne hij.symm,Equiv.swap_apply_left,Function.comp_apply]
    rw [mul_div_cancel_right₀ _ hj,mul_div_cancel_left₀ _ hi]
  · by_cases hkj : k = j
    · subst k
      simp only [Function.update_self,Function.update_of_ne hij.symm,
        Equiv.swap_apply_right,Function.comp_apply]
      exact mul_div_cancel_right₀ _ hj
    · simp only [Function.update_of_ne hki,Function.update_of_ne hkj,
        Function.comp_apply,Equiv.swap_apply_of_ne_of_ne hki hkj]

theorem rvReindexVolume_finiteVolume (U : RVObject (M := M) S n) (e : Equiv.Perm (Fin n))
    (hU : U.volume.FiniteFibres) : (U.reindexVolume e).volume.FiniteFibres := by
  apply finiteFibres_of_value_reflection U.volume _ hU
  intro u v he
  exact (rvReindexMap_bijective S e).1 he

theorem exists_rv_transposition_chain (U : RVObject (M := M) S n) (i j : Fin n)
    (hij : i ≠ j) (hUF : U.volume.FiniteFibres)
    (hU : ∀ u k, (U.value u k).val ≠ iRVZero) :
    ∃ T : RVUnaryChain S n U (U.reindexVolume (Equiv.swap i j)),
      (∀ u, T.iso.hom.map u = u) ∧ T.finiteVolume := by
  let A := rvCoordinateArithmeticObject U .multiply i j
  have hAF := rvCoordinateArithmeticObject_finiteVolume U .multiply i j hij hUF hU
  have hA := rvCoordinateArithmeticObject_nonzero U .multiply i j hU
  let B := rvCoordinateArithmeticObject A .divideFrom j i
  have hBF := rvCoordinateArithmeticObject_finiteVolume A .divideFrom j i hij.symm hAF hA
  have hB := rvCoordinateArithmeticObject_nonzero A .divideFrom j i hA
  let C := rvCoordinateArithmeticObject B .divide i j
  have hCF := rvCoordinateArithmeticObject_finiteVolume B .divide i j hij hBF hB
  have hC := rvCoordinateArithmeticObject_nonzero B .divide i j hB
  have hValue (u : U.domain) : C.value u = (U.reindexVolume (Equiv.swap i j)).value u := by
    change (rvCoordinateArithmeticObject B .divide i j).value u = _
    rw [rvCoordinateArithmeticObject_value]
    change Function.update (B.value u) i (B.value u i / B.value u j) = _
    dsimp only [B]
    rw [rvCoordinateArithmeticObject_value]
    change Function.update (Function.update (A.value u) j (A.value u i / A.value u j)) i
      ((Function.update (A.value u) j (A.value u i / A.value u j)) i /
        (Function.update (A.value u) j (A.value u i / A.value u j)) j) = _
    dsimp only [A]
    rw [rvCoordinateArithmeticObject_value]
    exact rv_coordinate_swap_arithmetic (U.value u) i j hij
      ((rv_nonzero_code_iff _).mp (hU u i)) ((rv_nonzero_code_iff _).mp (hU u j))
  let a := rvCoordinateArithmeticIso U .multiply i j hij hUF hU
  let b := rvCoordinateArithmeticIso A .divideFrom j i hij.symm hAF hA
  let c := rvCoordinateArithmeticIso B .divide i j hij hBF hB
  let d : C ≅ U.reindexVolume (Equiv.swap i j) :=
    rvIsoOfVolumePreservingBijection (Map.id C.domain) Function.bijective_id
      (fun u => (hValue u).symm)
  have hd : RVUnaryRelativeAt d.hom.map i := by
    intro u k hk
    exact (congrFun (hValue u) k).symm
  let T : RVUnaryChain S n U (U.reindexVolume (Equiv.swap i j)) :=
    .step i a (rvCoordinateArithmeticIso_unary U .multiply i j hij hUF hU)
      (.step j b (rvCoordinateArithmeticIso_unary A .divideFrom j i hij.symm hAF hA)
        (.step i c (rvCoordinateArithmeticIso_unary B .divide i j hij hBF hB)
          (.step i d hd (.identity _))))
  exact ⟨T,fun _ => rfl,hUF,hAF,hBF,hCF,rvReindexVolume_finiteVolume U _ hUF⟩

end DiamondIntegral.Section6
