import «section 3».GammaGroundRVUnitFormNormalForm
import «section 3».RVNonzeroTupleCoding
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

/-- Local measured product normal form on the entire actual RV tuple
domain, including every zero-coordinate stratum. -/
theorem gammaGroundRV_form_normal_form {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (A : GammaGroundDefSet hc B (rawRVSpace (M := M) n))
    (ω : GammaGroundMap A (GammaGroundDefSet.univ hc B (volumeGammaSpace hc)))
    (w : (rawRVSpace (M := M) n).Carrier → Values.Gamma (M := M))
    (hω : ∀ a : A, w a.val = (ω a).val) :
    ∃ N : ℕ, ∃ C : Fin N → GammaGroundRVFormProductChart hc B (rawRVSpace (M := M) n) w,
      (∀ i j, i ≠ j → Disjoint (C i).source.carrier (C j).source.carrier) ∧
      (∀ x, x ∈ A.carrier ↔ ∃ i, x ∈ (C i).source.carrier) := by
  let e := gammaGroundRVNonzeroTupleCodeBijection h00 A
  let I := (gammaGroundRVNonzeroTupleCodeMap A).image
  let ωI := ω.comp e.symm.map
  let v := fun z => if hz : z ∈ I.carrier then (ωI ⟨z,hz⟩).val else (1 : Values.Gamma (M := M))
  have hv : ∀ z : I, v z.val = (ωI z).val := fun z => dif_pos z.property
  obtain ⟨N,C,hdis,hcov⟩ := gammaGroundRVUnit_form_normal_form hκ hs h00 hsmall hγsmall hΓ I ωI v hv
  have hsub : ∀ i, (C i).source.carrier ⊆ I.carrier := fun i x hx => (hcov x).mpr ⟨i,hx⟩
  have hwe : ∀ a : A, w a.val = v (e.map a).val := by
    intro a
    rw [hv (e.map a)]
    change w a.val = (ω (e.symm.map (e.map a))).val
    rw [GammaGroundBijection.symm,GammaGroundMap.inverse_apply]
    exact hω a
  let D := fun i => (C i).pullback e (hsub i) w hwe
  refine ⟨N,D,?_,?_⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    rintro x ⟨a,ha,hai⟩ ⟨b,hb,hbj⟩
    have hab : a = b := Subtype.ext (ha.trans hb.symm)
    rw [hab] at hai
    exact Set.disjoint_left.mp (hdis i j hij) hai hbj
  · intro x
    constructor
    · intro hx
      let a : A := ⟨x,hx⟩
      obtain ⟨i,hi⟩ := (hcov (e.map a).val).mp (e.map a).property
      exact ⟨i,a,rfl,hi⟩
    · rintro ⟨i,hx⟩
      exact e.inverseImage_subset (C i).source hx
end DiamondIntegral.Section3
