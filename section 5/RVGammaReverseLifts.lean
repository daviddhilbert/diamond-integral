import «section 5».RVGammaFamilyLifts
import «section 5».UnitTupleReindexMaps

/-! Reversing the Gamma-code block is an actual coordinate bijection,
and makes each cylindrical-tree step append its new RV coordinate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p n : ℕ}

def reverseSuffixPermutation (p n : ℕ) : Equiv.Perm (Fin (p+n)) :=
  finSumFinEquiv.symm.trans (((Equiv.refl (Fin p)).sumCongr (Fin.revPerm)).trans finSumFinEquiv)

theorem reverseSuffixPermutation_left (i : Fin p) :
    reverseSuffixPermutation p n (Fin.castAdd n i) = Fin.castAdd n i := by
  simp [reverseSuffixPermutation]

theorem reverseSuffixPermutation_right (j : Fin n) :
    reverseSuffixPermutation p n (Fin.natAdd p j) = Fin.natAdd p j.rev := by
  simp [reverseSuffixPermutation]

def rvGammaReverseLift
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) p).prod ((volumeGammaSpace hc).power (Fin n)))) :
    GammaGroundDefSet hc B (rawRVUnitSpace (M := M) (p+n)) :=
  ⟨{u | (u ∘ Fin.castAdd n, rvUnitTupleValues (u ∘ Fin.natAdd p ∘ Fin.rev)) ∈ T.carrier},
    by
      have h := (rvGammaFamilyLift T).definable.preimage (unitTupleReindexMap B.real (reverseSuffixPermutation p n))
      apply h.congr
      intro u
      change ((u ∘ reverseSuffixPermutation p n) ∘ Fin.castAdd n,
        rvUnitTupleValues ((u ∘ reverseSuffixPermutation p n) ∘ Fin.natAdd p)) ∈ T.carrier ↔ _
      have hl : (u ∘ reverseSuffixPermutation p n) ∘ Fin.castAdd n = u ∘ Fin.castAdd n := by
        funext j; simp only [Function.comp_def, reverseSuffixPermutation_left]
      have hr : (u ∘ reverseSuffixPermutation p n) ∘ Fin.natAdd p = u ∘ Fin.natAdd p ∘ Fin.rev := by
        funext j; simp only [Function.comp_def, reverseSuffixPermutation_right]
      rw [hl,hr]
      rfl⟩

end DiamondIntegral.Section5
