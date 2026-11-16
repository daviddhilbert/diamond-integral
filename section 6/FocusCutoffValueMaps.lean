import «section 6».FullFocusCovarianceData
import «section 6».ScalarGammaValues
import «section 6».NamedGammaFibreValues

/-! The aperture cutoff has an actual definable Gamma graph on the
full current focus domain. No particular coordinate of the RV labels
is required to store the active leading term. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}

def scalarFocusProductMap {A : DefSet (rawMixedSpace (M := M) n r) S}
    {B : DefSet (rawVFSpace (M := M) 1) S} (f : Map A B)
    (c : VF M) (hc : S.Definable₁ LRV {c.val}) :
    Map A (DefSet.univ (rawVFSpace (M := M) 1) S) := by
  let P := rawMixedSpace (M := M) n r
  let Q := rawVFSpace (M := M) 1
  let F (z : Fin n ⊕ Fin r → M) : Fin 1 → M := fun _ => iVFMul c.val (scalarCodeExtension f z)
  let g (p : Mixed M n r) : Fin 1 → VF M := fun _ =>
    c*⟨scalarCodeExtension f (mixedValues p),scalarCodeExtension_isVF f _⟩
  have hF : S.DefinableMap LRV F := fun _ => scalarMulCode_definable
    (definable_named_constant c.val hc) (scalarCodeExtension_definable f)
  have hCode (z : P.domain) : vfValues (g (P.decode z))=F z.val := by
    change (fun _ => iVFMul c.val (scalarCodeExtension f (mixedValues (P.decode z))))=F z.val
    rw [mixedValues_decode]
  have hDom (z : P.domain) : F z.val ∈ Q.domain := ⟨g (P.decode z),hCode z⟩
  refine Map.ofCodes A g F hF hDom ?_
  intro z
  exact vfValues_injective ((vfValues_decode ⟨_,hDom z⟩).trans (hCode z).symm)

theorem scalarFocusProductMap_at {A : DefSet (rawMixedSpace (M := M) n r) S}
    {B : DefSet (rawVFSpace (M := M) 1) S} (f : Map A B)
    (c : VF M) (hc : S.Definable₁ LRV {c.val}) (p : A) :
    (scalarFocusProductMap f c hc p).val 0=c*(f p).val 0 := by
  change c*⟨scalarCodeExtension f (mixedValues p.val),scalarCodeExtension_isVF f _⟩=c*(f p).val 0
  exact congrArg (fun x : VF M => c*x) (Subtype.ext (scalarCodeExtension_at f p))

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

def CentripetalData.cutoffGammaMap (D : CentripetalData (G := G) A) :
    Map (focusActive A D.activeTags) (DefSet.univ (rawGammaPresentation (M := M)) S) :=
  (scalarGammaValueMap S).comp (scalarFocusProductMap D.focusMap D.coefficient D.coefficient_definable)

theorem CentripetalData.cutoffGammaMap_value (D : CentripetalData (G := G) A)
    (p : focusActive A D.activeTags) : (D.cutoffGammaMap p).val.val=
      vfValue (D.coefficient*D.extendedFocus p.val) :=
  scalarGammaValueMap_nonzero S _ (mul_ne_zero D.coefficient_nonzero
    (D.focus_nonzero p.property.1 p.property.2))

end DiamondIntegral.Section6
