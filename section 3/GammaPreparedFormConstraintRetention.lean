import «section 3».GammaPreparedFormConstraints

/-! The full prepared relation retains the Gamma equality predicate,
not only its values on previously selected fibres. -/
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

theorem gammaFormConstraintIndices_append (z : Fin p → M) (r : Fin a → M) (s : Fin b → M) :
    Fin.append (Fin.append z r) s ∘ gammaFormConstraintIndices p a b = Fin.append r s := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp only [gammaFormConstraintIndices,Function.comp_apply,Fin.addCases_left,Fin.addCases_right,
      Fin.append_left,Fin.append_right]

theorem gammaPrepared_relation_form_constraint
    (A : GammaGroundDefSet hc B (rawRVSpace (M := M) a))
    (D : GammaGroundDefSet hc B (rawRVSpace (M := M) b))
    (ω : GammaGroundVolumeForm hc B A) (π : GammaGroundVolumeForm hc B D)
    {X : SpecialTransformations.Section5.DefSet (M := M) S p 0}
    {Z : SpecialTransformations.Section5.DefSet (M := M) S p l}
    (T : SpecialBijection X Z) (hT : GammaChainDefinable B T.chain)
    (H : GammaRelationFormula B p a b (fun _ => .vf))
    (hH : H.val ⊆ gammaParametricFormConstraint A D ω π (fun _ => .vf)) :
    ((GammaParameterRecode.prepared T hT).relation H).val ⊆
      gammaParametricFormConstraint A D ω π (fun _ => .rv) := by
  let H' := (GammaParameterRecode.prepared T hT).relation H
  intro w hw
  have hs := H'.property.proper w hw
  let t : Fin (p+l) → RV (M := M) := fun j => ⟨w (Fin.castAdd b (Fin.castAdd a j)),by
    simpa only [Fin.append_left,sortEval,iRV] using hs (Fin.castAdd b (Fin.castAdd a j))⟩
  let r : Fin a → RV (M := M) := fun j => ⟨w (Fin.castAdd b (Fin.natAdd (p+l) j)),by
    simpa only [Fin.append_left,Fin.append_right,sortEval,iRV] using hs (Fin.castAdd b (Fin.natAdd (p+l) j))⟩
  let s : Fin b → RV (M := M) := fun j => ⟨w (Fin.natAdd ((p+l)+a) j),by
    simpa only [Fin.append_right,sortEval,iRV] using hs (Fin.natAdd ((p+l)+a) j)⟩
  have hp : Fin.append (Fin.append (rvValues t) (rvValues r)) (rvValues s) = w := by
    change Fin.append (Fin.append (fun j => w (Fin.castAdd b (Fin.castAdd a j)))
      (fun j => w (Fin.castAdd b (Fin.natAdd (p+l) j)))) (fun j => w (Fin.natAdd ((p+l)+a) j)) = w
    have hl := Fin.append_castAdd_natAdd (f := fun j : Fin ((p+l)+a) => w (Fin.castAdd b j))
    exact (congrArg (fun v => Fin.append v (fun j => w (Fin.natAdd ((p+l)+a) j))) hl).trans
      (Fin.append_castAdd_natAdd (f := w))
  have hf := ((H.flatten.preparedDescend T hT).unflattenRV_append t r s).mp (hp.symm ▸ hw)
  have hr := (gammaRawRVGraph_append_iff _ (Fin.elim0,t) (Fin.elim0,Fin.append r s)).mp hf
  obtain ⟨q,_,hrow⟩ := hr
  have hraw := (H.vfRelation_append (T.inverseMap q).val r s).mp hrow
  have hprior := (hH hraw).1
  change Fin.append (Fin.append _ _) _ ∘ gammaFormConstraintIndices p a b ∈ _ at hprior
  rw [gammaFormConstraintIndices_append] at hprior
  refine ⟨?_,hs⟩
  change w ∘ gammaFormConstraintIndices (p+l) a b ∈ _
  rw [← hp,gammaFormConstraintIndices_append]
  exact hprior

end DiamondIntegral.Section3
