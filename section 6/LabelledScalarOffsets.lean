import «section 6».UniformFinitePairedCores
import «section 6».AmbientCorePreparation

/-! Actual offset maps on a label-separated center family descend to
the existing RV labels and extend to their ambient active domain. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r : ℕ}
variable (E : DefSet (rawMixedSpace (M := M) 1 r) S)
variable (hUnique : ∀ p q : E,p.val.2=q.val.2 → p=q)
variable (e : Map E (DefSet.univ (rawVFSpace (M := M) 1) S))

def unaryLabelScalarMap : Map (pureRVTagDomain E) (DefSet.univ (rawVFSpace (M := M) 1) S) :=
  definableSurjectiveDescent (pureRVTagQuotient E) (pureRVTagQuotient_surjective E) e
    (fun p q he => congrArg e (hUnique p q ((pureRVTagQuotient_eq_iff E p q).mp he)))

theorem unaryLabelScalarMap_at (p : E) :
    unaryLabelScalarMap E hUnique e (pureRVTagQuotient E p)=e p :=
  definableSurjectiveDescent_apply _ _ _ _ p

def unaryLabelScalar (u : Fin r → RVInfinity M) : VF M :=
  if hu : u ∈ (pureRVTagDomain E).carrier then (unaryLabelScalarMap E hUnique e ⟨u,hu⟩).val 0 else 0

theorem unaryLabelScalar_at (p : E) : unaryLabelScalar E hUnique e p.val.2=(e p).val 0 := by
  have hu : p.val.2 ∈ (pureRVTagDomain E).carrier := (pureRVTagQuotient E p).property
  rw [unaryLabelScalar,dif_pos hu]
  exact congrArg (fun q => q.val 0) (unaryLabelScalarMap_at E hUnique e p)

variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}

def unaryAmbientScalarMap : Map (focusActive A (pureRVTagDomain E)) (DefSet.univ (rawVFSpace (M := M) 1) S) :=
  (unaryLabelScalarMap E hUnique e).comp (unaryCenterActiveLabelMap E)

theorem unaryAmbientScalarMap_value (p : focusActive A (pureRVTagDomain E)) :
    (unaryAmbientScalarMap E hUnique e p).val 0=unaryLabelScalar E hUnique e p.val.2 := by
  change (unaryLabelScalarMap E hUnique e ⟨p.val.2,p.property.2⟩).val 0=unaryLabelScalar E hUnique e p.val.2
  rw [unaryLabelScalar,dif_pos p.property.2]

theorem unaryLabelScalar_nonzero (he : ∀ p : E,(e p).val 0 ≠ 0)
    (u : Fin r → RVInfinity M) (hu : u ∈ (pureRVTagDomain E).carrier) :
    unaryLabelScalar E hUnique e u ≠ 0 := by
  obtain ⟨p,hp⟩ := pureRVTagQuotient_surjective E ⟨u,hu⟩
  have hpu : p.val.2=u := congrArg Subtype.val hp
  rw [← hpu,unaryLabelScalar_at]
  exact he p

theorem unaryLabelScalar_small (he : ∀ p : E,vfValue (p.val.1 0) < vfValue ((e p).val 0))
    (u : Fin r → RVInfinity M) (hu : u ∈ (pureRVTagDomain E).carrier) :
    vfValue (unaryLabelCenter E hUnique u) < vfValue (unaryLabelScalar E hUnique e u) := by
  obtain ⟨p,hp⟩ := pureRVTagQuotient_surjective E ⟨u,hu⟩
  have hpu : p.val.2=u := congrArg Subtype.val hp
  rw [← hpu,unaryLabelCenter_at,unaryLabelScalar_at]
  exact he p

end DiamondIntegral.Section6
