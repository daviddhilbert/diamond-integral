import «section 6».GammaCoreComponentSemantics

/-! Whole-program admissibility includes core-form compatibility at
every actual centripetal stage. Intermediate Gamma graphs are transported
by the full transition, and the resulting test is original-base definable. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p q n r s k : ℕ}

namespace CentripetalProgramTemplate

def coreFormGood : {r s : ℕ} → CentripetalProgramTemplate (M := M) S p n r s →
    MixedSetParameterTemplate (M := M) S p n r → GammaFormParameterTemplate (M := M) S p n r → Set (Fin p → M)
  | _,_,.identity _,_,_ => Set.univ
  | _,_,.regularize _,_,_ => Set.univ
  | r,_,.centripetal T,A,W =>
      gammaCoreConstantParameterLocus (focusComponentTransition T A) W.graph T.coordinate (Fin.castAdd r (0 : Fin 1))
  | _,_,.comp F H,A,W => F.coreFormGood A W ∩ H.coreFormGood (F.target A) (W.transport (F.transition A))

theorem coreFormGood_definable (T : CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r) (W : GammaFormParameterTemplate (M := M) S p n r) :
    S.Definable LRV (T.coreFormGood A W) := by
  induction T with
  | identity r => exact Set.definable_univ
  | regularize r => exact Set.definable_univ
  | centripetal T =>
    exact gammaCoreConstantParameterLocus_definable (focusComponentTransition T A) W.graph
      (focusComponentTransition_definable T A) W.definable T.coordinate _
  | comp F H ihF ihH => exact (ihF A W).inter (ihH (F.target A) (W.transport (F.transition A)))

def measuredFormGood (T : CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (W : GammaFormParameterTemplate (M := M) S p n r) : Set (Fin p → M) :=
  T.measuredGood A P W ∩ T.coreFormGood A W

theorem measuredFormGood_definable (T : CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r)
    (W : GammaFormParameterTemplate (M := M) S p n r) : S.Definable LRV (T.measuredFormGood A P W) :=
  (T.measuredGood_definable A P W).inter (T.coreFormGood_definable A W)

end CentripetalProgramTemplate

theorem gammaCoreConstantParameterLocus_substitute
    (R : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin s)) → M))
    (W : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (rawGammaPresentation (M := M)).Index) → M))
    (h : DefinableParameterSubstitution (M := M) S p q) (j : Fin n) (coreTag : Fin s) :
    gammaCoreConstantParameterLocus (parameterSubstitution h R) (parameterSubstitution h W) j coreTag=
      h.value ⁻¹' gammaCoreConstantParameterLocus R W j coreTag := by
  ext a
  rfl

theorem CentripetalProgramTemplate.substitute_coreFormGood
    (T : CentripetalProgramTemplate (M := M) S p n r s)
    (h : DefinableParameterSubstitution (M := M) S p q)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (W : GammaFormParameterTemplate (M := M) S p n r) :
    (T.substitute h).coreFormGood (A.substitute h) (W.substitute h)=h.value ⁻¹' T.coreFormGood A W := by
  induction T with
  | identity r => rfl
  | regularize r => rfl
  | centripetal T =>
    change gammaCoreConstantParameterLocus (focusComponentTransition (T.substitute h) (A.substitute h))
      (parameterSubstitution h W.graph) _ _=_
    rw [focusComponentTransition_substitute]
    exact gammaCoreConstantParameterLocus_substitute _ _ h _ _
  | comp F H ihF ihH =>
    have hTransport := W.transport_substitute (F.transition A)
      ((F.substitute h).transition (A.substitute h)) h (F.substitute_transition h A)
    change (F.substitute h).coreFormGood (A.substitute h) (W.substitute h) ∩
      (H.substitute h).coreFormGood ((F.substitute h).target (A.substitute h))
        ((W.substitute h).transport ((F.substitute h).transition (A.substitute h)))=_
    rw [← hTransport,F.substitute_target h A,ihF A W,ihH (F.target A) (W.transport (F.transition A))]
    rfl

end DiamondIntegral.Section6
