import «section 3».GammaGroundFiniteSupport
import Section3.SmallFiniteParameters
import Section3.VFAlgebraicity

/-! A finite collection of Gamma-ground formulas can be interpreted over
one small real parameter expansion consisting only of RV codes. This is
an interpretation, not descent of arbitrary sets over the expanded base. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}

theorem realCodeParameters_small {P : Space LRV M} {S : Set M} (c : P.domain)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hS : Cardinal.mk S < κ) :
    Cardinal.mk (realCodeParameters S c) < κ := by
  letI : Finite P.Index := P.finiteIndex
  exact small_union_finite hκ S hS _ (Set.finite_range c.val)

theorem gammaPowerCode_rv {n : ℕ} (c : ((volumeGammaSpace hc).power (Fin n)).domain)
    (i : ((volumeGammaSpace hc).power (Fin n)).Index) : iRV (c.val i) := by
  change Fin n × Fin 1 at i
  rcases i with ⟨i, j⟩
  have hj : j = 0 := Fin.eq_zero j
  subst j
  exact (c.property i).1

theorem gammaPowerCode_parameterField {n : ℕ} {S : Set M}
    (c : ((volumeGammaSpace hc).power (Fin n)).domain) :
    vfParameterField (realCodeParameters S c) = vfParameterField S := by
  apply vfParameterField_union_rv
  rintro t ⟨i, rfl⟩
  exact gammaPowerCode_rv c i

theorem GammaGroundDefinable.realizeFinite {n : ℕ} (Q : Fin n → Space LRV M)
    (A : ∀ i, Set (Q i).Carrier) (hA : ∀ i, GammaGroundDefinable hc ground (Q i) (A i))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hS : Cardinal.mk ground.real < κ) :
    ∃ T : Set M, ground.real ⊆ T ∧ Cardinal.mk T < κ ∧
      vfParameterField T = vfParameterField ground.real ∧ ∀ i, (Q i).Definable T (A i) := by
  obtain ⟨k, γ, hγ, h⟩ := GammaGroundDefinable.finiteSupport Q A hA
  obtain ⟨c, hcγ⟩ := ((volumeGammaSpace hc).power (Fin k)).onto γ
  exact ⟨realCodeParameters ground.real c, Set.subset_union_left,
    realCodeParameters_small c hκ hS, gammaPowerCode_parameterField c,
    fun i => (h i).over_real_code c hcγ⟩

theorem GammaGroundDefinable.realize {Q : Space LRV M} {A : Set Q.Carrier}
    (hA : GammaGroundDefinable hc ground Q A)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hS : Cardinal.mk ground.real < κ) :
    ∃ T : Set M, ground.real ⊆ T ∧ Cardinal.mk T < κ ∧
      vfParameterField T = vfParameterField ground.real ∧ Q.Definable T A := by
  obtain ⟨T, hT, hs, hf, hd⟩ := GammaGroundDefinable.realizeFinite
    (fun _ : Fin 1 => Q) (fun _ => A) (fun _ => hA) hκ hS
  exact ⟨T, hT, hs, hf, hd 0⟩

end DiamondIntegral.Section3
