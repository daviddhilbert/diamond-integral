import «section 3».GammaGroundMapImages
import «section 3».NamedMapComposition
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}
variable {P Q : Space LRV M}

/-- Unique fibres of any original-ground definable interpreted relation
form an original-ground definable set. -/
theorem gammaGroundDefinable_unique_fibre {R : Set (P.prod Q).Carrier}
    (hR : GammaGroundDefinable hc B (P.prod Q) R) :
    GammaGroundDefinable hc B P {p | ∃! q, (p,q) ∈ R} := by
  let T := P.prod (Q.prod Q)
  let fP := universalProductFst P (Q.prod Q) B.real
  let fQ := universalProductSnd P (Q.prod Q) B.real
  have h1 := hR.preimage (universalTripleFirstSecond P Q Q B.real)
  have h2 := hR.preimage (universalTripleFirstThird P Q Q B.real)
  have hEq : GammaGroundDefinable hc B (Q.prod Q) {z | z.1 = z.2} :=
    GammaGroundDefinable.of_real ((relationDefinable_iff_product Eq).mp (Q.relation_eq_definable B.real))
  have hbad := ((h1.inter h2).inter (hEq.compl.preimage fQ)).image fP
  have hex := hR.image (universalProductFst P Q B.real)
  apply (hex.inter hbad.compl).congr
  intro p
  change ((∃ z ∈ R, z.1 = p) ∧
    ¬ ∃ z : T.Carrier, (((z.1,z.2.1) ∈ R ∧ (z.1,z.2.2) ∈ R) ∧
      ¬ z.2.1 = z.2.2) ∧ z.1 = p) ↔ ∃! q, (p,q) ∈ R
  constructor
  · rintro ⟨⟨⟨p0,q⟩,hq,hp⟩,hnot⟩
    change p0 = p at hp
    subst p0
    refine ⟨q,hq,?_⟩
    intro q' hq'
    by_contra hne
    apply hnot
    exact ⟨(p,(q,q')),⟨⟨hq,hq'⟩,Ne.symm hne⟩,rfl⟩
  · rintro ⟨q,hq,hu⟩
    refine ⟨⟨(p,q),hq,rfl⟩,?_⟩
    rintro ⟨⟨p0,q1,q2⟩,⟨⟨h1,h2⟩,hne⟩,hp⟩
    change p0 = p at hp
    subst p0
    exact hne ((hu q1 h1).trans (hu q2 h2).symm)

/-- The function on the unique-fibre locus is definable by its complete
original relation. Its construction chooses no point on a non-singleton fibre. -/
def gammaGroundUniqueFibreFunction (R : GammaGroundDefSet hc B (P.prod Q)) :
    GammaGroundMap
      (⟨{p | ∃! q, (p,q) ∈ R.carrier},gammaGroundDefinable_unique_fibre R.definable⟩ :
        GammaGroundDefSet hc B P)
      (GammaGroundDefSet.univ hc B Q) where
  toFun p := ⟨Classical.choose p.property,Set.mem_univ _⟩
  graph_definable := by
    let A : GammaGroundDefSet hc B P :=
      ⟨{p | ∃! q, (p,q) ∈ R.carrier},gammaGroundDefinable_unique_fibre R.definable⟩
    have hA := A.definable.preimage (universalProductFst P Q B.real)
    apply (hA.inter R.definable).congr
    intro z
    constructor
    · rintro ⟨hz,hR⟩
      let a : A := ⟨z.1,hz⟩
      refine ⟨a,rfl,?_⟩
      exact (Classical.choose_spec a.property).2 z.2 hR |>.symm
    · rintro ⟨a,ha,hq⟩
      refine ⟨?_,?_⟩
      · change z.1 ∈ A.carrier
        exact ha ▸ a.property
      · have hr := (Classical.choose_spec a.property).1
        change Classical.choose a.property = z.2 at hq
        have he : (a.val,Classical.choose a.property) = z := Prod.ext ha hq
        exact he ▸ hr

@[simp] theorem gammaGroundUniqueFibreFunction_spec
    (R : GammaGroundDefSet hc B (P.prod Q))
    (p : (⟨{p | ∃! q, (p,q) ∈ R.carrier},gammaGroundDefinable_unique_fibre R.definable⟩ :
      GammaGroundDefSet hc B P)) :
    (p.val,(gammaGroundUniqueFibreFunction R p).val) ∈ R.carrier :=
  (Classical.choose_spec p.property).1
end DiamondIntegral.Section3
