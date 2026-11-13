import «section 3».GammaGroundRVFormProductCharts
import «section 3».GammaGroundRVFiniteValueFibres
import «section 3».RVAngularGammaWeights
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {Q : Space LRV M} {n m : ℕ}

/-- Fixing the finite residue-value support moves the entire weight of
a product chart onto its Gamma factor, with definability over the same ground. -/
theorem gammaGroundRVProduct_weight_refinement
    (X : GammaGroundDefSet hc B Q)
    (R : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (hfin : (rvUnitTupleValues '' R.carrier).Finite)
    (G : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin m)))
    (F : GammaGroundBijection X (R.prod (gammaGroundRVUnitGammaPreimage G)))
    (H : (Fin n ⊕ Fin m → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hH : FullGammaFunction (integrationGammaBase B) H)
    (w : Q.Carrier → Values.Gamma (M := M))
    (hw : ∀ a : X, w a.val = H (Sum.elim (rvUnitTupleValues (F.map a).val.1)
      (rvUnitTupleValues (F.map a).val.2))) :
    ∃ N : ℕ, ∃ C : Fin N → GammaGroundRVFormProductChart hc B Q w,
      (∀ i j, i ≠ j → Disjoint (C i).source.carrier (C j).source.carrier) ∧
      (∀ x, x ∈ X.carrier ↔ ∃ i, x ∈ (C i).source.carrier) := by
  obtain ⟨N,δ,R',hd,hR',hdis,hcov⟩ := gammaGroundRVUnit_finite_value_fibres R hfin
  have hsub : ∀ i, (R' i).carrier ⊆ R.carrier := fun i r hr => (hR' i ▸ hr).1
  let Z := fun i => (R' i).prod (gammaGroundRVUnitGammaPreimage G)
  have hZ : ∀ i, (Z i).carrier ⊆ (R.prod (gammaGroundRVUnitGammaPreimage G)).carrier :=
    fun i _ hz => ⟨hsub i hz.1,hz.2⟩
  let Y := fun i => F.inverseImage (Z i)
  let E := fun i => F.restrictTarget (Z i) (hZ i)
  have hvalues : ∀ i (a : Y i), rvUnitTupleValues ((E i).map a).val.1 = δ i := by
    intro i a
    exact (hR' i ▸ ((E i).map a).property.1).2
  let C : Fin N → GammaGroundRVFormProductChart hc B Q w := fun i =>
    { source := Y i
      residueArity := n
      gammaArity := m
      residue := R' i
      gamma := G
      residue_finite := hfin.subset (Set.image_mono (hsub i))
      bijection := E i
      weight := fun γ => H (Sum.elim (δ i) γ)
      weight_definable := hH.freezeLeft (δ i) (hd i)
      preserves := fun a => by
        have hh := hw ⟨a.val,F.inverseImage_subset (Z i) a.property⟩
        change w a.val = H (Sum.elim (rvUnitTupleValues ((E i).map a).val.1)
          (rvUnitTupleValues ((E i).map a).val.2)) at hh
        rw [hvalues i a] at hh
        exact hh }
  refine ⟨N,C,?_,?_⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    rintro x ⟨a,ha,hai⟩ ⟨b,hb,hbj⟩
    have hab : a = b := Subtype.ext (ha.trans hb.symm)
    rw [hab] at hai
    exact Set.disjoint_left.mp (hdis i j hij) hai.1 hbj.1
  · intro x
    constructor
    · intro hx
      let a : X := ⟨x,hx⟩
      obtain ⟨i,hi⟩ := (hcov (F.map a).val.1).mp (F.map a).property.1
      exact ⟨i,a,rfl,hi,(F.map a).property.2⟩
    · rintro ⟨i,hx⟩
      exact F.inverseImage_subset (Z i) hx
end DiamondIntegral.Section3
