import «section 3».GammaSpecialJacobian
import Section5.TransformGeometry

/-! A special chain retains each original RV label at an explicit final
coordinate. Arbitrary functions of all original labels can therefore be
transported through the chain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section5
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n m l r : ℕ}
variable {A : SpecialTransformations.Section5.DefSet (M := M) S n m}
variable {D : SpecialTransformations.Section5.DefSet (M := M) S n l}
variable {E : SpecialTransformations.Section5.DefSet (M := M) S n r}

def gammaPrimitiveOldLabelIndex (p : Primitive S n A D) : Fin m → Fin l :=
  match p with
  | .canonical _ => Fin.natAdd n
  | .centripetal _ => id

theorem gammaPrimitive_old_labels (p : Primitive S n A D) (a : A) :
    (p.toMap a).val.2 ∘ gammaPrimitiveOldLabelIndex p = a.val.2 := by
  cases p with
  | canonical A =>
    funext i
    exact canonical_old a.val i
  | centripetal D => exact D.toFocusGeometry.eta_labels a.val

def gammaChainOldLabelIndex :
    {m l : ℕ} → {A : SpecialTransformations.Section5.DefSet (M := M) S n m} →
      {D : SpecialTransformations.Section5.DefSet (M := M) S n l} →
      Chain S n A D → Fin m → Fin l
  | _,_,_,_,.nil _,i => i
  | _,_,_,_,.cons p tail,i => gammaChainOldLabelIndex tail (gammaPrimitiveOldLabelIndex p i)

theorem gammaChain_old_labels (T : Chain S n A D) (a : A) :
    (T.toMap a).val.2 ∘ gammaChainOldLabelIndex T = a.val.2 := by
  induction T with
  | nil A => rfl
  | cons p tail ih =>
    funext i
    exact (congrFun (ih (p.toMap a)) (gammaPrimitiveOldLabelIndex p i)).trans
      (congrFun (gammaPrimitive_old_labels p a) i)

theorem gammaSpecial_inverse_old_labels (T : SpecialBijection A D) (a : D) :
    (T.inverseMap a).val.2 = a.val.2 ∘ gammaChainOldLabelIndex T.chain := by
  have h := gammaChain_old_labels T.chain (T.inverseMap a)
  change (T.toMap (T.inverseMap a)).val.2 ∘ gammaChainOldLabelIndex T.chain = _ at h
  rw [T.apply_inverse] at h
  exact h.symm

end DiamondIntegral.Section3
