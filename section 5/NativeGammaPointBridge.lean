import «section 5».NativeMixedSortedRealization
import IntegrationSection6.GammaPointSortedIsomorphisms

/-! Actual original-Gamma point sets and special-map graphs realize native
mixed domains and bijections with exactly the same parameters. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section6
open DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n r m s : ℕ}

theorem nativeMixedCode_eq_gammaPointCode (q : Point (M := M) n r) : nativeMixedCode q = gammaPointCode q := rfl

def nativeGammaPointDomain (A : Set (Point (M := M) n r)) (hA : GammaSetDefinable B A) :
    GammaGroundDefSet hc B (rawMixedSpace (M := M) n r) where
  carrier := A
  definable := by
    apply (nativeMixedOfRaw (hc := hc) (gammaPointCode '' A) hA).definable.congr
    intro q
    change (∃ z ∈ A,gammaPointCode z = nativeMixedCode q) ↔ q ∈ A
    constructor
    · rintro ⟨z,hz,hzq⟩
      exact nativeMixedCode_injective hzq ▸ hz
    · exact fun hq => ⟨q,hq,rfl⟩

def nativeGammaPointBijection {A : Set (Point (M := M) n r)} {C : Set (Point (M := M) m s)}
    (hA : GammaSetDefinable B A) (hC : GammaSetDefinable B C) (e : GammaIso B A C) :
    GammaGroundBijection (nativeGammaPointDomain (hc := hc) A hA) (nativeGammaPointDomain C hC) :=
  nativeMixedBijectionOfSortedIso _ _ (IntegrationInACVF.Section6.GammaIso.toSortedIso e)

theorem nativeGammaPointBijection_apply {A : Set (Point (M := M) n r)} {C : Set (Point (M := M) m s)}
    (hA : GammaSetDefinable B A) (hC : GammaSetDefinable B C) (e : GammaIso B A C)
    (a : nativeGammaPointDomain (hc := hc) A hA) :
    ((nativeGammaPointBijection hA hC e).map a).val = (e.equiv ⟨a.val,a.property⟩).val := by
  change ((pointSetCodeEquiv C).symm ((pointSetCodeEquiv C)
    (e.equiv ((pointSetCodeEquiv A).symm ((pointSetCodeEquiv A) ⟨a.val,a.property⟩))))).val = _
  rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]

theorem nativeGammaPointBijection_symm_apply {A : Set (Point (M := M) n r)} {C : Set (Point (M := M) m s)}
    (hA : GammaSetDefinable B A) (hC : GammaSetDefinable B C) (e : GammaIso B A C)
    (c : nativeGammaPointDomain (hc := hc) C hC) :
    ((nativeGammaPointBijection hA hC e).symm.map c).val = (e.equiv.symm ⟨c.val,c.property⟩).val := by
  let a : nativeGammaPointDomain (hc := hc) A hA :=
    ⟨(e.equiv.symm ⟨c.val,c.property⟩).val,(e.equiv.symm ⟨c.val,c.property⟩).property⟩
  have ha : (nativeGammaPointBijection hA hC e).map a = c := by
    apply Subtype.ext
    rw [nativeGammaPointBijection_apply]
    exact congrArg Subtype.val (e.equiv.apply_symm_apply ⟨c.val,c.property⟩)
  have hi := (nativeGammaPointBijection hA hC e).map.inverse_apply
    (nativeGammaPointBijection hA hC e).bijective a
  rw [ha] at hi
  exact congrArg Subtype.val hi

end DiamondIntegral.Section5
