import «section 4».GammaIteratedIntegral

/-! Iterated Euler integrals depend on the actual integer-valued
function, independently of an equivalent presentation of its parameters. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section4 GammaDefinableEuler GammaIntegerFamilies GammaWeightedFamilies GammaIteratedIntegral EulerFunction
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (B C : Base (M := M)) (hrB : Cardinal.mk B.real < κ) (hγB : Cardinal.mk B.gamma < κ)
variable (hrC : Cardinal.mk C.real < κ) (hγC : Cardinal.mk C.gamma < κ) (kind : EulerKind)

theorem gamma_integral_parameter_independent (n : ℕ) (f : familySubgroup B n) (g : familySubgroup C n)
    (hfg : ∀ x,f.val x = g.val x) :
    integrateAll h00 hκ hs B hrB hγB kind n f = integrateAll h00 hκ hs C hrC hγC kind n g := by
  induction n with
  | zero => exact hfg emptyTuple
  | succ n ih =>
    apply ih
    intro y
    change totalEuler kind (fibreFunction h00 B kind f.val f.property y) =
      totalEuler kind (fibreFunction h00 C kind g.val g.property y)
    apply congrArg (totalEuler kind)
    apply eval_injective kind
    funext t
    obtain ⟨γ,rfl⟩ := toPaperGamma.surjective t
    exact (fibreFunction_eval h00 B kind f.val f.property y γ).trans
      ((hfg (Fin.cons γ y)).trans (fibreFunction_eval h00 C kind g.val g.property y γ).symm)

end DiamondIntegral.Section5
