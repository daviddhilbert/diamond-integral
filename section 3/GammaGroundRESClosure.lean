import «section 3».GammaGroundRVProducts
import «section 3».GammaGroundRVCoproducts

/-! Finite source-value support survives actual cartesian products
and tagged disjoint unions over the full Gamma ground. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {n m k l : ℕ}

theorem GammaGroundRVObject.product_res {U : GammaGroundRVObject hc ground k} {V : GammaGroundRVObject hc ground l}
    (hU : gammaGroundResProperty U) (hV : gammaGroundResProperty V) : gammaGroundResProperty (U.product V) := by
  let appendValues (p : (Fin U.arity → Section2.GammaInfinity M) ×
      (Fin V.arity → Section2.GammaInfinity M)) := Fin.append p.1 p.2
  apply ((hU.prod hV).image appendValues).subset
  rintro _ ⟨t, ⟨a, ha⟩, rfl⟩
  let u : U.domain := ⟨a.val.1, a.property.1⟩
  let v : V.domain := ⟨a.val.2, a.property.2⟩
  refine ⟨((fun i => Values.vrv (u.val i)), (fun i => Values.vrv (v.val i))),
    ⟨⟨u.val, u.property, rfl⟩, ⟨v.val, v.property, rfl⟩⟩, ?_⟩
  change Fin.append (fun i => Values.vrv (u.val i)) (fun i => Values.vrv (v.val i)) = _
  rw [← ha]
  funext i
  change Fin.append (fun j => Values.vrv (u.val j)) (fun j => Values.vrv (v.val j)) i =
    Values.vrv (rvAppend a.val.1 a.val.2 i)
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp only [rvAppend, Fin.append_left, Fin.append_right] <;> rfl


theorem GammaGroundRVObject.coprod_res {U V : GammaGroundRVObject hc ground k}
    (hU : gammaGroundResProperty U) (hV : gammaGroundResProperty V) : gammaGroundResProperty (U.coprod V) := by
  let z : Section2.GammaInfinity M := Values.vrv (⟨iRVZero, rv_zero_mem (by infer_instance : M ⊨ Axioms.ACVF)⟩ : CanonicalRV.RVSort M)
  let o : Section2.GammaInfinity M := Values.vrv (⟨iRVOne, rv_one_mem (by infer_instance : M ⊨ Axioms.ACVF)⟩ : CanonicalRV.RVSort M)
  let L (γ : Fin U.arity → Section2.GammaInfinity M) :=
    Fin.append (fun _ : Fin 1 => z) (Fin.append γ (fun _ : Fin V.arity => z))
  let R (γ : Fin V.arity → Section2.GammaInfinity M) :=
    Fin.append (fun _ : Fin 1 => o) (Fin.append (fun _ : Fin U.arity => z) γ)
  apply ((hU.image L).union (hV.image R)).subset
  rintro _ ⟨t, ht, rfl⟩
  rcases ht with ⟨u, hu⟩ | ⟨v, hv⟩
  · left
    refine ⟨fun i => Values.vrv (u.val i), ⟨u.val, u.property, rfl⟩, ?_⟩
    rw [← hu]
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [L, z, gammaGroundRVLeftTag, GammaGroundMap.ofGlobal, rvLeftTagMap, rvMapOfCode, Map.ofCodes, rvLeftTag, Fin.append_left]
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp only [L, gammaGroundRVLeftTag, GammaGroundMap.ofGlobal, rvLeftTagMap, rvMapOfCode, Map.ofCodes, rvLeftTag, rvAppend,
          Fin.append_right, Fin.append_left]
      · simp only [L, z, gammaGroundRVLeftTag, GammaGroundMap.ofGlobal, rvLeftTagMap, rvMapOfCode, Map.ofCodes, rvLeftTag, rvAppend,
          rvZeroTuple, Fin.append_right]
  · right
    refine ⟨fun i => Values.vrv (v.val i), ⟨v.val, v.property, rfl⟩, ?_⟩
    rw [← hv]
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [R, o, gammaGroundRVRightTag, GammaGroundMap.ofGlobal, rvRightTagMap, rvMapOfCode, Map.ofCodes, rvRightTag, Fin.append_left]
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp only [R, z, gammaGroundRVRightTag, GammaGroundMap.ofGlobal, rvRightTagMap, rvMapOfCode, Map.ofCodes, rvRightTag, rvAppend,
          rvZeroTuple, Fin.append_right, Fin.append_left]
      · simp only [R, gammaGroundRVRightTag, GammaGroundMap.ofGlobal, rvRightTagMap, rvMapOfCode, Map.ofCodes, rvRightTag, rvAppend,
          Fin.append_right]

end DiamondIntegral.Section3
