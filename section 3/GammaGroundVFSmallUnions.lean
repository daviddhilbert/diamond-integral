import «section 3».GammaGroundRealization
import «section 3».GammaGroundDefSets
import «section 3».VFDimensionComparison
import Section4.VFUnions
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaGroundVF_small_union_iff {n r : ℕ}
    (A B : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hS : Cardinal.mk ground.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) (hn : 0 < n) :
    Section2.vfDimension (A.union B).carrier < (n : WithBot ℕ) ↔
      Section2.vfDimension A.carrier < (n : WithBot ℕ) ∧
      Section2.vfDimension B.carrier < (n : WithBot ℕ) := by
  have h : ∀ i : Fin 2, GammaGroundDefinable hc ground (rawMixedSpace n r) (![A.carrier, B.carrier] i) := by
    intro i
    fin_cases i
    · exact A.definable
    · exact B.definable
  obtain ⟨T, hT, hsmall, hfield, hd⟩ := GammaGroundDefinable.realizeFinite
    (fun _ : Fin 2 => rawMixedSpace n r) ![A.carrier, B.carrier] h hκ hS
  let DA : DefSet (rawMixedSpace (M := M) n r) T := ⟨A.carrier, hd 0⟩
  let DB : DefSet (rawMixedSpace (M := M) n r) T := ⟨B.carrier, hd 1⟩
  change Section2.vfDimension (DA.union DB).carrier < (n : WithBot ℕ) ↔
    Section2.vfDimension DA.carrier < (n : WithBot ℕ) ∧ Section2.vfDimension DB.carrier < (n : WithBot ℕ)
  rw [vf_small_iff_companion hc hs hsmall hv hn,
    vfDim_union hc hs hsmall (rawRVSpace 1) (rawRVSpace_rvCoded 1), max_lt_iff,
    ← vf_small_iff_companion hc hs hsmall hv hn DA,
    ← vf_small_iff_companion hc hs hsmall hv hn DB]

end DiamondIntegral.Section3
