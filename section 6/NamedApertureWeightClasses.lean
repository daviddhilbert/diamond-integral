import «section 6».UnaryCentripetalDiscTrace
import «section 6».FiniteApertureProfiles

/-! Actual named aperture multipliers preserve the value-subgroup
class of a unary core's radius times its inherited form. The source
radius is the radius of the current polydisc; the result does not assume
that the absolute aperture is globally constant. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def namedVFValueSubgroup (S : Set M) : Subgroup (Gamma M) :=
  Subgroup.closure {γ | ∃ c : VF M, ∃ hc : c ≠ 0,
    S.Definable₁ LRV {c.val} ∧ finiteValue c hc = γ}

theorem namedVFValueSubgroup_contains {S : Set M} (c : VF M) (hc : c ≠ 0)
    (hDef : S.Definable₁ LRV {c.val}) : finiteValue c hc ∈ namedVFValueSubgroup S :=
  Subgroup.subset_closure ⟨c,hc,hDef,rfl⟩

theorem namedVFValueSubgroup_le {S : Set M} (H : Subgroup (Gamma M))
    (hH : ∀ c : VF M, ∀ hc : c ≠ 0,
      S.Definable₁ LRV {c.val} → finiteValue c hc ∈ H) : namedVFValueSubgroup S ≤ H := by
  apply (Subgroup.closure_le H).2
  rintro γ ⟨c,hc,hDef,rfl⟩
  exact hH c hc hDef

namespace CentripetalData

variable {r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}

theorem coefficient_value_mem_namedSubgroup (D : CentripetalData (G := G) A) :
    finiteValue D.coefficient D.coefficient_nonzero ∈ namedVFValueSubgroup S :=
  namedVFValueSubgroup_contains D.coefficient D.coefficient_nonzero D.coefficient_definable

theorem unary_point_nonzero (D : CentripetalData (G := G) A) (p : A) :
    (D.point p.val).1 0 ≠ 0 := by
  apply D.image_vfDoublyBounded.nonzero (i := 0)
  rw [D.image_carrier]
  exact ⟨p.val,p.property,rfl⟩

theorem unary_core_finiteValue (D : CentripetalData (G := G) A) (p : A)
    (hu : p.val.2 ∈ D.activeTags.carrier) (hCore : D.core p.val = true) :
    finiteValue ((D.point p.val).1 0) (D.unary_point_nonzero p) =
      finiteValue D.coefficient D.coefficient_nonzero *
        finiteValue (p.val.1 0) (D.sourceDoublyBounded.nonzero p.property 0) := by
  apply Subtype.ext
  have h := D.core_output_value p.property hu hCore
  have hcoord : D.coordinate = 0 := Subsingleton.elim _ _
  change vfValue ((D.point p.val).1 0) = vfValue D.coefficient * vfValue (p.val.1 0)
  simpa only [hcoord] using h

theorem unary_core_weight_class (D : CentripetalData (G := G) A) (p : A)
    (hu : p.val.2 ∈ D.activeTags.carrier) (hCore : D.core p.val = true) (η : Gamma M) :
    ((finiteValue ((D.point p.val).1 0) (D.unary_point_nonzero p) * η : Gamma M) :
        Gamma M ⧸ namedVFValueSubgroup S) =
      ((finiteValue (p.val.1 0) (D.sourceDoublyBounded.nonzero p.property 0) * η : Gamma M) :
        Gamma M ⧸ namedVFValueSubgroup S) := by
  apply QuotientGroup.eq_iff_div_mem.mpr
  rw [D.unary_core_finiteValue p hu hCore]
  have he (c r : Gamma M) : (c*r*η)/(r*η) = c := by
    rw [mul_assoc,mul_div_cancel_right]
  rw [he]
  exact D.coefficient_value_mem_namedSubgroup

end CentripetalData
end DiamondIntegral.Section6
