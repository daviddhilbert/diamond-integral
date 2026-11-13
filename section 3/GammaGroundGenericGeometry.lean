import «section 3».GammaGroundVFDimension
import «section 3».GammaGroundDefSets
import «section 3».EssentialVFGerms

/-! Independence over the original VF field detects smaller-dimensional
exceptional sets even when their definitions use Gamma parameters. -/
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
variable {n r : ℕ}

def GammaGroundGeneric (A : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r)) :=
  {a : A // AlgebraicIndependent (vfParameterField ground.real) a.val.1}

theorem gammaGround_independent_not_mem
    (E : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hS : Cardinal.mk ground.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) (hn : 0 < n)
    (hE : Section2.vfDimension E.carrier < (n : WithBot ℕ))
    (a : (rawMixedSpace (M := M) n r).Carrier)
    (ha : AlgebraicIndependent (vfParameterField ground.real) a.1) : a ∉ E.carrier := by
  obtain ⟨T, hT, hsmall, hfield, hd⟩ := E.definable.realize hκ hS
  let D : DefSet (rawMixedSpace (M := M) n r) T := ⟨E.carrier, hd⟩
  have hD : vfDim (rawRVSpace 1) D < n := (vf_small_iff_companion hc hs hsmall hv hn D).mp hE
  have haT : AlgebraicIndependent (vfParameterField T) a.1 := by rwa [hfield]
  exact EssentialVFMap.independent_not_mem hc D hD a haT

theorem gammaGround_mem_of_small_complement
    {A : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r)}
    (E : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hS : Cardinal.mk ground.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) (hn : 0 < n)
    (hE : Section2.vfDimension (A.sdiff E).carrier < (n : WithBot ℕ))
    (a : GammaGroundGeneric A) : a.val.val ∈ E.carrier := by
  by_contra he
  exact gammaGround_independent_not_mem (A.sdiff E) hκ hs hS hv hn hE a.val.val a.property ⟨a.val.property, he⟩

theorem gammaGround_small_complement_of_generic
    (A E : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n r))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hS : Cardinal.mk ground.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) (hn : 0 < n)
    (hE : ∀ a : GammaGroundGeneric A, a.val.val ∈ E.carrier) :
    Section2.vfDimension (A.sdiff E).carrier < (n : WithBot ℕ) := by
  have h : ∀ i : Fin 2, GammaGroundDefinable hc ground (rawMixedSpace n r) (![A.carrier, E.carrier] i) := by
    intro i
    fin_cases i
    · exact A.definable
    · exact E.definable
  obtain ⟨T, hT, hsmall, hfield, hd⟩ := GammaGroundDefinable.realizeFinite
    (fun _ : Fin 2 => rawMixedSpace n r) ![A.carrier, E.carrier] h hκ hS
  let DA : DefSet (rawMixedSpace (M := M) n r) T := ⟨A.carrier, hd 0⟩
  let DE : DefSet (rawMixedSpace (M := M) n r) T := ⟨E.carrier, hd 1⟩
  have hgen : ∀ a : EssentialVFMap.Generic DA, a.val.val ∈ DE.carrier := by
    intro a
    have ha : AlgebraicIndependent (vfParameterField ground.real) a.val.val.1 := by
      rw [← hfield]
      exact a.property
    exact hE ⟨a.val, ha⟩
  exact (vf_small_iff_companion hc hs hsmall hv hn (DA.sdiff DE)).mpr
    (EssentialVFMap.small_complement_of_generic hc hs hsmall hn DE hgen)

end DiamondIntegral.Section3
