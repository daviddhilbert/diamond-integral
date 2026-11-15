import IntegrationSection5.TraceFlags

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m l : ℕ} {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}

def fullRVProjectionInto {a b : ℕ} (ρ : Fin a → Fin b)
    (X : DefSet (M := M) S n b) (Y : DefSet (M := M) S n a)
    (hXY : ∀ p ∈ carrier X, fullRVProjection ρ p ∈ carrier Y) : Map X Y :=
  Map.mk (fun p => ⟨fullRVProjection ρ p.val,hXY _ p.property⟩)
    (Map.graph_definable (fullRVProjectionMap ρ X))

namespace UniformRelativeTrace

def inputPresentation (T : UniformRelativeTrace S n A B) := rvGraph T.flagMap

def inputProjection (T : UniformRelativeTrace S n A B) : Map T.inputPresentation A :=
  fullRVProjectionInto (Fin.castAdd T.flagCount) T.inputPresentation A (by
    rintro q ⟨p,rfl⟩
    have he : fullRVProjection (Fin.castAdd T.flagCount) (attachRV p.val (T.flagMap p).val.2) = p.val := by
      refine Prod.ext rfl ?_
      funext j
      exact Fin.append_left _ _ j
    exact he.symm ▸ p.property)

theorem inputProjection_bijective (T : UniformRelativeTrace S n A B) : Function.Bijective T.inputProjection := by
  have hEq (a : A) : T.inputProjection ⟨attachRV a.val (T.flagMap a).val.2,⟨a,rfl⟩⟩ = a := by
    apply Subtype.ext
    refine Prod.ext rfl ?_
    funext j
    exact Fin.append_left _ _ j
  constructor
  · rintro ⟨p,a,rfl⟩ ⟨q,b,rfl⟩ he
    have hab : a = b := (hEq a).symm.trans (he.trans (hEq b))
    subst b
    rfl
  · intro a
    exact ⟨⟨attachRV a.val (T.flagMap a).val.2,⟨a,rfl⟩⟩,hEq a⟩


end UniformRelativeTrace
end IntegrationInACVF.Section5
