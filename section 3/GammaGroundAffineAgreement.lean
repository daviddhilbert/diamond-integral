import «section 3».GammaGroundRVUnitAffineMaps
import «section 3».GammaGroundMapImages
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {n : ℕ}

/-- Formulas use actual old-ground coefficients and unimodular integer
matrices. They carry no additional residue or Gamma parameters. -/
structure OriginalGroundAffineRVFormula (hc : CanonicalStructure.IsCanonical (M := M))
    (B : GammaParameters.Base (M := M)) (n : ℕ) where
  matrix : Matrix (Fin n) (Fin n) ℤ
  det_unit : IsUnit matrix.det
  coefficient : Fin n → (CanonicalRV.RVSort M)ˣ
  coefficient_definable : GammaGroundDefinable hc B (rawRVUnitSpace n) {coefficient}

variable (G J : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin n)))
variable (h : GammaGroundMap G J) (F : OriginalGroundAffineRVFormula hc B n)

def gammaGroundAffineValueMap :
    GammaGroundMap (gammaGroundRVUnitGammaPreimage G)
      (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin n))) :=
  (GammaGroundMap.ofGlobal _ _ (rvUnitGammaMap hc B.real n) (fun _ => Set.mem_univ _)).comp
    (gammaGroundRVUnitAffineMap (gammaGroundRVUnitGammaPreimage G) F.matrix F.coefficient F.coefficient_definable)

def gammaGroundAffineAgreement : GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin n)) :=
  ((gammaGroundFullPreimageValueMap G).restrict
    ((gammaGroundAffineValueMap G F).equalizer_subset (h.toUniv.comp (gammaGroundFullPreimageValueMap G)))).image

theorem gammaGroundAffineAgreement_subset : (gammaGroundAffineAgreement G J h F).carrier ⊆ G.carrier := by
  rintro γ ⟨a,rfl⟩
  exact ((gammaGroundFullPreimageValueMap G).restrict
    ((gammaGroundAffineValueMap G F).equalizer_subset (h.toUniv.comp (gammaGroundFullPreimageValueMap G))) a).property

/-- Agreement is a genuine same-ground Gamma predicate. Definability
is obtained from full RV graphs rather than from named value representatives. -/
theorem gammaGroundAffineAgreement_mem (γ : G) :
    γ.val ∈ (gammaGroundAffineAgreement G J h F).carrier ↔
      (h γ).val = rvUnitTupleValues F.coefficient *
        integerMonomialMap (G := Values.Gamma (M := M)) F.matrix γ.val := by
  let A := gammaGroundRVUnitGammaPreimage G
  let w := gammaGroundAffineValueMap G F
  let E := w.equalizer (h.toUniv.comp (gammaGroundFullPreimageValueMap G))
  have hw (a : A) : (w a).val = rvUnitTupleValues F.coefficient *
      integerMonomialMap F.matrix (rvUnitTupleValues a.val) :=
    gammaGroundRVUnitAffineMap_values A F.matrix F.coefficient F.coefficient_definable a
  constructor
  · rintro ⟨u,hu⟩
    obtain ⟨a,ha,he⟩ := u.property
    have hv : gammaGroundFullPreimageValueMap G a = γ := by
      apply Subtype.ext
      exact (congrArg rvUnitTupleValues ha).trans hu
    change (w a).val = (h (gammaGroundFullPreimageValueMap G a)).val at he
    rw [hv] at he
    have hval : rvUnitTupleValues a.val = γ.val := congrArg Subtype.val hv
    exact he.symm.trans ((hw a).trans (congrArg
      (fun t => rvUnitTupleValues F.coefficient * integerMonomialMap F.matrix t) hval))
  · intro hγ
    obtain ⟨u,hu⟩ := rvUnitTupleValues_surjective (M := M) n γ.val
    have huA : u ∈ A.carrier := by
      change rvUnitTupleValues u ∈ G.carrier
      exact hu.symm ▸ γ.property
    let a : A := ⟨u,huA⟩
    have hv : gammaGroundFullPreimageValueMap G a = γ := Subtype.ext hu
    have he : (w a).val = (h.toUniv.comp (gammaGroundFullPreimageValueMap G) a).val := by
      change (w a).val = (h (gammaGroundFullPreimageValueMap G a)).val
      rw [hw,hv,hu,hγ]
    exact ⟨⟨u,⟨a,rfl,he⟩⟩,hu⟩

end DiamondIntegral.Section3
