import «section 5».RVGammaFibreEulerValues
import «section 5».RVGammaFamilyLifts

/-! Restriction to an original-ground RV base piece preserves complete
source rows and whole Euler validity on that piece. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p n : ℕ}

def rvGammaFamilyRestrict
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) p).prod ((volumeGammaSpace hc).power (Fin n))))
    (A : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) p)) :=
  T.inter ⟨{z | z.1 ∈ A.carrier},A.definable.preimage
    (universalProductFst (rawRVUnitSpace p) ((volumeGammaSpace hc).power (Fin n)) B.real)⟩

theorem rvGammaFamilySchema_restrict_row
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) p).prod ((volumeGammaSpace hc).power (Fin n))))
    (A : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) p)) (x : A) (v : Fin n → M) :
    (gammaDomainSyntax hc B (rvGammaFamilySchema T)).Realize
      (Sum.elim (predicateParameterValues B (rvUnitValues x.val)) v) ↔
    (gammaDomainSyntax hc B (rvGammaFamilySchema (rvGammaFamilyRestrict T A))).Realize
      (Sum.elim (predicateParameterValues B (rvUnitValues x.val)) v) := by
  refine (rvGammaFamilySchema_represents T x.val v).trans ?_
  refine (and_congr_right (fun _ => ?_)).trans (rvGammaFamilySchema_represents (rvGammaFamilyRestrict T A) x.val v).symm
  change (x.val,codeValue ∘ v) ∈ T.carrier ↔
    ((x.val,codeValue ∘ v) ∈ T.carrier ∧ x.val ∈ A.carrier)
  exact (and_iff_left x.property).symm

theorem OriginalEulerCertificate.validFor_source_congr
    (C : OriginalEulerCertificate B (fun _ : Fin p => .rv) n)
    (D F : GammaDomainFormula B p n (fun _ => .rv)) (z : Fin p → M)
    (hrow : ∀ v : Fin n → M,
      (gammaDomainSyntax hc B D).Realize (Sum.elim (predicateParameterValues B z) v) ↔
      (gammaDomainSyntax hc B F).Realize (Sum.elim (predicateParameterValues B z) v)) :
    C.ValidFor hc D z ↔ C.ValidFor hc F z := by
  simp only [OriginalEulerCertificate.ValidFor,EulerFormulaCertificate.validity,Formula.realize_inf]
  exact and_congr Iff.rfl (finitePartitionValidity_congr _ _ _ _ _ _ hrow (fun _ _ => Iff.rfl))

theorem rvGammaFamilyLift_restrict_partition
    (X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) p))
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) p).prod ((volumeGammaSpace hc).power (Fin n))))
    (hproj : ∀ x γ, (x,γ) ∈ T.carrier → x ∈ X.carrier)
    {ι : Type} [Fintype ι] (A : ι → GammaGroundDefSet hc B (rawRVUnitSpace (M := M) p))
    (hd : ∀ i j, i ≠ j → Disjoint (A i).carrier (A j).carrier)
    (hcov : ∀ x, x ∈ X.carrier ↔ ∃ i, x ∈ (A i).carrier) :
    (∀ i j, i ≠ j → Disjoint (rvGammaFamilyLift (rvGammaFamilyRestrict T (A i))).carrier
      (rvGammaFamilyLift (rvGammaFamilyRestrict T (A j))).carrier) ∧
    ∀ u, u ∈ (rvGammaFamilyLift T).carrier ↔ ∃ i, u ∈ (rvGammaFamilyLift (rvGammaFamilyRestrict T (A i))).carrier := by
  constructor
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro u hi hj
    exact Set.disjoint_left.mp (hd i j hij) hi.2 hj.2
  · intro u
    constructor
    · intro hu
      obtain ⟨i,hi⟩ := (hcov _).mp (hproj _ _ hu)
      exact ⟨i,hu,hi⟩
    · rintro ⟨i,hi⟩
      exact hi.1

end DiamondIntegral.Section5
