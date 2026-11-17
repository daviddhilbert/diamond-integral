import «section 3».GammaGroundMapBinaryPieces
import «section 3».GammaGroundConstants
import «section 3».GammaGroundMapComposition
import «section 3».RVFamilyRealization

/-! A binary original-ground predicate has an actual finite RV tag.
The two absolute zero/one tags require no Gamma representative choice. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.realSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}
variable {Q : Space LRV M}

def gammaGroundRVBinaryConstant (A : GammaGroundDefSet hc B Q) (i : Fin 2) :
    GammaGroundMap A (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) 2)) := by
  let Z := GammaGroundDefSet.univ hc B (rawRVSpace (M := M) 0)
  have hZ : GammaGroundDefinable hc B (rawRVSpace (M := M) 0) ({Fin.elim0} : Set (Fin 0 → CanonicalRV.RVSort M)) := by
    apply Z.definable.congr
    intro z
    exact ⟨fun _ => funext (fun j => Fin.elim0 j),fun _ => Set.mem_univ _⟩
  let e := GammaGroundMap.const (R := rawRVSpace (M := M) 0) A (Fin.elim0 : Fin 0 → CanonicalRV.RVSort M) hZ
  let f := GammaGroundMap.ofGlobal Z (GammaGroundDefSet.univ hc B (rawRVSpace 2))
    (rvFamilyTagMap i (DefSet.univ (rawRVSpace 0) B.real)) (fun _ => Set.mem_univ _)
  exact f.comp e

theorem gammaGroundRVBinaryConstant_value (A : GammaGroundDefSet hc B Q) (i : Fin 2) (p : A) :
    (gammaGroundRVBinaryConstant A i p).val = rvFamilyTag i := by
  funext j
  change Fin.append (rvFamilyTag i) (Fin.elim0 : Fin 0 → CanonicalRV.RVSort M) j = rvFamilyTag i j
  exact Fin.append_left (rvFamilyTag i) Fin.elim0 j

def gammaGroundRVBinaryClassifier (A D : GammaGroundDefSet hc B Q) :
    GammaGroundMap A (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) 2)) :=
  (gammaGroundRVBinaryConstant A 0).binaryPieces (gammaGroundRVBinaryConstant A 1) D

theorem gammaGroundRVBinaryClassifier_value (A D : GammaGroundDefSet hc B Q) (p : A) :
    (gammaGroundRVBinaryClassifier A D p).val = if p.val ∈ D.carrier then rvFamilyTag 0 else rvFamilyTag 1 := by
  change (if p.val ∈ D.carrier then gammaGroundRVBinaryConstant A 0 p else gammaGroundRVBinaryConstant A 1 p).val = _
  split <;> rw [gammaGroundRVBinaryConstant_value]

theorem gammaGroundRVBinaryClassifier_mem (A D : GammaGroundDefSet hc B Q) (p : A) :
    (gammaGroundRVBinaryClassifier A D p).val = rvFamilyTag 0 ↔ p.val ∈ D.carrier := by
  rw [gammaGroundRVBinaryClassifier_value]
  by_cases hp : p.val ∈ D.carrier
  · rw [ite_eq_left hp]
    exact ⟨fun _ => hp,fun _ => rfl⟩
  · rw [ite_eq_right hp]
    constructor
    · intro h
      have he := rvFamilyTag_injective h
      have h01 : (1 : Fin 2) ≠ 0 := by decide
      exact False.elim (h01 he)
    · exact fun h => False.elim (hp h)

end DiamondIntegral.Section3
