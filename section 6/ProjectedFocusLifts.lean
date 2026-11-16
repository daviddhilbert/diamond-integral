import «section 6».BoundedApertureCoefficients

/-! A continuous actual focus on the projected active domain lifts
over every protected source piece with its complete original-base graph. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}

def projectedActiveDomain (A : DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (U : DefSet (rawRVSpace (M := M) r) S) := (vfDropLast (focusActive A U)).image

theorem projectedActiveDomain_properInvariant
    (A : DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (U : DefSet (rawRVSpace (M := M) r) S) (hA : ProperInvariant S A.carrier) :
    ProperInvariant S (projectedActiveDomain A U).carrier :=
  vfDropLast_image_properInvariant (focusActive_properInvariant A hA U)

variable {A P : DefSet (rawMixedSpace (M := M) (n+1) r) S}
variable {U : DefSet (rawRVSpace (M := M) r) S}

def protectedFocusProjection (hPA : P.carrier ⊆ A.carrier) :
    Map (focusActive P U) (projectedActiveDomain A U) :=
  (vfDropLast (focusActive A U)).toImage.comp
    (Map.inclusion (fun _ hp => ⟨hPA hp.1,hp.2⟩))

def projectedFocusLift (f : Map (projectedActiveDomain A U) (DefSet.univ (rawVFSpace (M := M) 1) S))
    (hPA : P.carrier ⊆ A.carrier) : Map (focusActive P U) (DefSet.univ (rawVFSpace (M := M) 1) S) :=
  f.comp (protectedFocusProjection hPA)

theorem init_update_last (a : Fin (n+1) → VF M) (x : VF M) :
    Fin.init (Function.update a (Fin.last n) x) = Fin.init a := by
  funext i
  simp only [Fin.init,Function.update_of_ne (Fin.castSucc_ne_last i)]

theorem projectedFocusLift_value
    (f : Map (projectedActiveDomain A U) (DefSet.univ (rawVFSpace (M := M) 1) S))
    (hPA : P.carrier ⊆ A.carrier) (p : focusActive P U) :
    (projectedFocusLift f hPA p).val 0 = totalFocusFibre f p.val.2 (Fin.init p.val.1) 0 := by
  let q := protectedFocusProjection (U := U) hPA p
  exact (congrFun (totalFocusFibre_at f q.val.2 q.val.1 q.property) 0).symm

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem projectedFocusLift_continuousOn
    (f : Map (projectedActiveDomain A U) (DefSet.univ (rawVFSpace (M := M) 1) S))
    (hPA : P.carrier ⊆ A.carrier) (hf : ∀ u, Continuous (FMT.focusFibre f u))
    (u : Fin r → RVInfinity M) (hu : u ∈ U.carrier) :
    ContinuousOn (fun x : Fin (n+1) → VF M => totalFocusFibre f u (Fin.init x) 0) (vfFibre P.carrier u) := by
  have hScalar : ContinuousOn (fun x => totalFocusFibre f u x 0)
      (vfFibre (projectedActiveDomain A U).carrier u) :=
    (continuous_apply 0).comp_continuousOn (totalFocusFibre_continuousOn f u (hf u))
  have hInit : Continuous (Fin.init : (Fin (n+1) → VF M) → Fin n → VF M) :=
    continuous_pi (fun i => continuous_apply i.castSucc)
  exact hScalar.comp hInit.continuousOn (fun x hx => ⟨⟨(x,u),hPA hx,hu⟩,rfl⟩)

end DiamondIntegral.Section6
