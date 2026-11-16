import «section 6».UnaryContextLifts

/-! Exact coordinates of the actual inverse ambient unary lift. The
old first coordinate is recovered from the unary inverse and its labels;
all inactive VF coordinates stay fixed and all old labels are selected. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.UnaryContextLift
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s m : ℕ} {I : Type*}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S} {B : DefSet (rawMixedSpace (M := M) 1 s) S}
variable {i : Fin m} {X : UnaryPreparationContext A i} {f : Map A B}
variable {P : I → DefSet (rawMixedSpace (M := M) m X.arity) S}

theorem inverse_projection (h00 : M ⊨ Axioms.ACVF00)
    (F : UnaryContextLift (G := G) X f P) (hf : Function.Bijective f) (q : F.target.source) :
    X.projection (F.map.inverse (F.chain.toChain.toSpecial.bijective h00) q)=
      f.inverse hf (F.target.projection q) := by
  apply hf.injective
  rw [Map.apply_inverse]
  have h := F.commutes (F.map.inverse (F.chain.toChain.toSpecial.bijective h00) q)
  rw [Map.apply_inverse] at h
  exact h.symm

theorem inverse_inactive (h00 : M ⊨ Axioms.ACVF00)
    (F : UnaryContextLift (G := G) X f P) (q : F.target.source) (j : Fin m) (hj : j ≠ i) :
    (F.map.inverse (F.chain.toChain.toSpecial.bijective h00) q).val.1 j=q.val.1 j := by
  have h := F.fixed (F.map.inverse (F.chain.toChain.toSpecial.bijective h00) q) j hj
  rw [Map.apply_inverse] at h
  exact h.symm

theorem inverse_retained (h00 : M ⊨ Axioms.ACVF00)
    (F : UnaryContextLift (G := G) X f P) (q : F.target.source) (j : Fin X.arity) :
    (F.map.inverse (F.chain.toChain.toSpecial.bijective h00) q).val.2 j=
      q.val.2 (F.retainedLabels j) := by
  have h := F.retained (F.map.inverse (F.chain.toChain.toSpecial.bijective h00) q) j
  rw [Map.apply_inverse] at h
  exact h.symm

theorem inverse_head_value (h00 : M ⊨ Axioms.ACVF00)
    {X : UnaryPreparationContext A (0 : Fin (n+1))}
    {P : I → DefSet (rawMixedSpace (M := M) (n+1) X.arity) S}
    (F : UnaryContextLift (G := G) X f P) (hf : Function.Bijective f) (q : F.target.source) :
    (F.map.inverse (F.chain.toChain.toSpecial.bijective h00) q).val=
      (Fin.cons ((f.inverse hf (F.target.projection q)).val.1 0) (Fin.tail q.val.1),
        q.val.2 ∘ F.retainedLabels) := by
  apply Prod.ext
  · funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · have h := congrArg (fun a : A => a.val.1 0) (F.inverse_projection h00 hf q)
      rw [X.projection_value] at h
      exact h
    · exact F.inverse_inactive h00 q k.succ (Fin.succ_ne_zero k)
  · funext j
    exact F.inverse_retained h00 q j

end DiamondIntegral.Section6.UnaryContextLift
