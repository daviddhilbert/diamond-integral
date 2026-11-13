import «section 3».GammaGroundRVNonzeroProductNormalForm
import «section 3».RVNonzeroTupleCoding
import «section 3».GammaGroundBijectionRestrictions
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

/-- An original-ground product chart with the original RV tuple source,
including zero coordinates. Ambient factor arities do not specify RV[k]. -/
structure GammaGroundRVProductChart (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) (n : ℕ) where
  source : GammaGroundDefSet hc B (rawRVSpace (M := M) n)
  residueArity : ℕ
  gammaArity : ℕ
  residue : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) residueArity)
  gamma : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin gammaArity))
  residue_finite : (rvUnitTupleValues '' residue.carrier).Finite
  bijection : GammaGroundBijection source (residue.prod (gammaGroundRVUnitGammaPreimage gamma))

variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

/-- Finite disjoint geometric product normal form on the entire actual
RV tuple domain. The injective nonzero coding retains every zero tag. -/
theorem gammaGroundRV_product_normal_form {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) n)) :
    ∃ N : ℕ, ∃ D : Fin N → GammaGroundRVProductChart hc B n,
      (∀ i j, i ≠ j → Disjoint (D i).source.carrier (D j).source.carrier) ∧
      ∀ x, x ∈ X.carrier ↔ ∃ i, x ∈ (D i).source.carrier := by
  let e := gammaGroundRVNonzeroTupleCodeBijection h00 X
  let I := (gammaGroundRVNonzeroTupleCodeMap X).image
  have hI := (gammaGroundRVUnit_definable_iff I.carrier).mp I.definable
  obtain ⟨N,C,hdis,hcov⟩ := gammaGroundRV_nonzero_product_normal_form (hc := hc) hκ hs h00 hsmall hγsmall hΓ
    (rvUnitValues '' I.carrier) hI
  have hsub : ∀ i, (C i).source.carrier ⊆ I.carrier := by
    intro i x hx
    obtain ⟨y,hy,he⟩ := (hcov x).mpr ⟨i,hx⟩
    exact rvUnitValues_injective he ▸ hy
  let Y := fun i => e.inverseImage (C i).source
  let D : Fin N → GammaGroundRVProductChart hc B n := fun i =>
    ⟨Y i,(C i).residueArity,(C i).gammaArity,(C i).residue,(C i).gamma,(C i).residue_finite,
      (C i).bijection.comp (e.restrictTarget (C i).source (hsub i))⟩
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
      let a : X := ⟨x,hx⟩
      have hi : rvUnitValues (e.map a).val ∈ rvUnitValues '' I.carrier :=
        ⟨(e.map a).val,(e.map a).property,rfl⟩
      obtain ⟨i,hxi⟩ := (hcov (e.map a).val).mp hi
      exact ⟨i,a,rfl,hxi⟩
    · rintro ⟨i,hx⟩
      exact e.inverseImage_subset (C i).source hx
end DiamondIntegral.Section3
