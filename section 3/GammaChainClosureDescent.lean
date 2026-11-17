import «section 3».GammaWeightedLiftClosureDescent
import IntegrationSection6.ElementaryLiftDiagram

/-! Auxiliary definable-closure names can be removed from every primitive
certificate in a special chain. In particular the elementary focus remains
a map over the original base, with the same underlying function. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section6
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n r s : ℕ}

theorem gammaSet_closure_descent {A : Set (Point (M := M) n r)}
    (hA : GammaSetDefinable (closureBase B) A) : GammaSetDefinable B A :=
  (DefinableOverBase.closureBase_iff B _ _).mp hA

theorem gammaGraph_closure_descent {u v : ℕ}
    {F : Point (M := M) n r → Point (M := M) u v → Prop}
    (hF : GammaGraphDefinable (closureBase B) F) : GammaGraphDefinable B F :=
  (DefinableOverBase.closureBase_iff B _ _).mp hF

theorem gammaFocus_closure_descent {A : SpecialTransformations.Section5.DefSet (M := M) S n r}
    {i : Fin n} {j : Fin r} {D : Focus A i j}
    (hD : GammaFocusDefinable (closureBase B) D) : GammaFocusDefinable B D :=
  ⟨gammaSet_closure_descent hD.1,gammaGraph_closure_descent hD.2⟩

theorem gammaPrimitive_closure_descent
    {A : SpecialTransformations.Section5.DefSet (M := M) S n r}
    {D : SpecialTransformations.Section5.DefSet (M := M) S n s}
    (T : Primitive S n A D) (hT : GammaPrimitiveDefinable (closureBase B) T) :
    GammaPrimitiveDefinable B T := by
  cases T with
  | canonical A => exact gammaSet_closure_descent hT
  | centripetal D => exact ⟨gammaSet_closure_descent hT.1,gammaFocus_closure_descent hT.2⟩

theorem gammaChain_closure_descent
    {A : SpecialTransformations.Section5.DefSet (M := M) S n r}
    {D : SpecialTransformations.Section5.DefSet (M := M) S n s}
    (T : Chain S n A D) (hT : GammaChainDefinable (closureBase B) T) :
    GammaChainDefinable B T := by
  induction T with
  | nil A => exact gammaSet_closure_descent hT
  | cons p tail ih => exact ⟨gammaPrimitive_closure_descent p hT.1,ih hT.2⟩

def gammaElementaryDiagram_closure_descent {U : GammaRVObject B n}
    (hU : (closureBase B).real ⊆ U.codes) {i : Fin n}
    (D : ElementaryLiftDiagram (gammaRVObjectClosure U hU) i) : ElementaryLiftDiagram U i where
  focus := D.focus
  full := D.full
  focus_graph := gammaFocus_closure_descent D.focus_graph
  admissible := D.admissible

end DiamondIntegral.Section3
