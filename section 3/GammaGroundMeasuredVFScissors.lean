import «section 3».GammaGroundMeasuredVFGerms
import «section 3».GammaGroundMeasuredVFZero
import «section 3».Grothendieck

/-! Actual measured VF scissors over all Gamma ground parameters.
Degree zero uses genuine form-preserving bijections; positive degree
uses the quotient of pointwise preserving essential representatives. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable [CharZero (Section2.VF M)]
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (hS : Cardinal.mk ground.real < κ)
variable (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

@[instance_reducible] def gammaGroundMeasuredVFGroupoid : ∀ n, Groupoid (GammaGroundMeasuredVFData hc ground n)
  | 0 => inferInstanceAs (Groupoid (GammaGroundZeroMeasuredVF hc ground))
  | k + 1 => gammaGroundPositiveMeasuredVFGroupoid hκ hs hS hv (Nat.zero_lt_succ k)

def GammaGroundMeasuredVFHom {n : ℕ} (U V : GammaGroundMeasuredVFData hc ground n) :=
  (gammaGroundMeasuredVFGroupoid hκ hs hS hv n).Hom U V

def gammaGroundMeasuredVFScissor {n : ℕ} (A B D E : GammaGroundMeasuredVFData hc ground n) : Prop :=
  ∃ U : GammaGroundMeasuredVFData hc ground n,
    ∃ X : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n U.arity),
    ∃ hX : X.carrier ⊆ U.domain.carrier,
      A = U.restrict X hX ∧ B = U.restrict (U.domain.sdiff X) (fun _ h => h.1) ∧
      D = U ∧ E = GammaGroundMeasuredVFData.empty hc ground n

def gammaGroundMeasuredVFPresentation (n : ℕ) : ScissorPresentation (GammaGroundMeasuredVFData hc ground n) where
  iso U V := Nonempty (GammaGroundMeasuredVFHom hκ hs hS hv U V)
  empty := GammaGroundMeasuredVFData.empty hc ground n
  scissor := gammaGroundMeasuredVFScissor

abbrev GammaGroundMeasuredVFKPlus (n : ℕ) := KPlus (gammaGroundMeasuredVFPresentation (hc := hc) (ground := ground) hκ hs hS hv n)

def gammaGroundMeasuredVFClass {n : ℕ} (U : GammaGroundMeasuredVFData hc ground n) :
    GammaGroundMeasuredVFKPlus (hc := hc) (ground := ground) hκ hs hS hv n := positiveClass (gammaGroundMeasuredVFPresentation (hc := hc) (ground := ground) hκ hs hS hv n) U

@[simp] theorem gammaGroundMeasuredVFClass_empty {n : ℕ} :
    gammaGroundMeasuredVFClass hκ hs hS hv (GammaGroundMeasuredVFData.empty hc ground n) = 0 :=
  positiveClass_empty (gammaGroundMeasuredVFPresentation (hc := hc) (ground := ground) hκ hs hS hv n)

theorem gammaGroundMeasuredVFClass_iso {n : ℕ} {U V : GammaGroundMeasuredVFData hc ground n}
    (f : GammaGroundMeasuredVFHom hκ hs hS hv U V) :
    gammaGroundMeasuredVFClass hκ hs hS hv U = gammaGroundMeasuredVFClass hκ hs hS hv V :=
  positiveClass_iso (gammaGroundMeasuredVFPresentation (hc := hc) (ground := ground) hκ hs hS hv n) ⟨f⟩

theorem gammaGroundMeasuredVFClass_scissor {n : ℕ} (U : GammaGroundMeasuredVFData hc ground n)
    (X : GammaGroundDefSet hc ground (rawMixedSpace (M := M) n U.arity)) (hX : X.carrier ⊆ U.domain.carrier) :
    gammaGroundMeasuredVFClass hκ hs hS hv (U.restrict X hX) +
      gammaGroundMeasuredVFClass hκ hs hS hv (U.restrict (U.domain.sdiff X) (fun _ h => h.1)) =
        gammaGroundMeasuredVFClass hκ hs hS hv U := by
  have h := positiveClass_scissor (gammaGroundMeasuredVFPresentation (hc := hc) (ground := ground) hκ hs hS hv n)
    ⟨U, X, hX, rfl, rfl, rfl, rfl⟩
  change gammaGroundMeasuredVFClass hκ hs hS hv _ + gammaGroundMeasuredVFClass hκ hs hS hv _ =
    gammaGroundMeasuredVFClass hκ hs hS hv _ + gammaGroundMeasuredVFClass hκ hs hS hv _ at h
  simpa only [gammaGroundMeasuredVFClass_empty, add_zero] using h

end DiamondIntegral.Section3
