import «section 3».GammaParametricFormConstraints
import Integration7.HKPreparedDensityConstraints

/-! Prepared recoding changes the base parameter only. Equality of
arbitrary retained Gamma forms therefore survives the complete recoded
relation, with no representative choice. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section6
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {S : Set M} {p l a b : ℕ}

theorem gammaPrepared_relation_form_eq
    (A : GammaGroundDefSet hc B (rawRVSpace (M := M) a))
    (D : GammaGroundDefSet hc B (rawRVSpace (M := M) b))
    (ω : GammaGroundVolumeForm hc B A) (π : GammaGroundVolumeForm hc B D)
    {X : SpecialTransformations.Section5.DefSet (M := M) S p 0}
    {Z : SpecialTransformations.Section5.DefSet (M := M) S p l}
    (T : SpecialBijection X Z) (hT : GammaChainDefinable B T.chain)
    (H : GammaRelationFormula B p a b (fun _ => .vf))
    (hH : H.val ⊆ gammaParametricFormConstraint A D ω π (fun _ => .vf))
    (t : Fin (p+l) → CanonicalRV.RVSort M) (u : A) (v : D)
    (h : Fin.append (Fin.append (rvValues t) (rvValues u.val)) (rvValues v.val) ∈
      ((GammaParameterRecode.prepared T hT).relation H).val) : ω u = π v := by
  have hf := ((H.flatten.preparedDescend T hT).unflattenRV_append t u.val v.val).mp h
  have hr := (gammaRawRVGraph_append_iff _ (Fin.elim0,t) (Fin.elim0,Fin.append u.val v.val)).mp hf
  obtain ⟨q,_,hrow⟩ := hr
  have hraw := (H.vfRelation_append (T.inverseMap q).val u.val v.val).mp hrow
  exact (gammaParametricFormConstraint_append A D ω π (fun _ => .vf) (vfValues (T.inverseMap q).val.1)
    (fun j => ((T.inverseMap q).val.1 j).property) u v).mp (hH hraw)

end DiamondIntegral.Section3
