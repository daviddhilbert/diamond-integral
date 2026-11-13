import «section 3».GammaGroundFiniteFamilies
import «section 3».GammaGroundMapImages
import «section 3».GammaGroundFiniteUnions
import «section 3».RVFamilyRealization

/-! Finite RV families have a genuine definable realization using finite
zero/one tags. The encoding is bijective and retains all original points. -/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {n : ℕ}

def gammaGroundRVFamilyTagMap {N : ℕ} (i : Fin N)
    (A : GammaGroundDefSet hc ground (rawRVSpace (M := M) n)) :
    GammaGroundMap A (GammaGroundDefSet.univ hc ground (rawRVSpace (N + n))) :=
  GammaGroundMap.ofGlobal _ _ (rvFamilyTagMap i (DefSet.univ (rawRVSpace n) ground.real)) (fun _ => Set.mem_univ _)

def GammaGroundFiniteFamily.rvRealization (A : GammaGroundFiniteFamily hc ground (rawRVSpace (M := M) n)) :
    GammaGroundDefSet hc ground (rawRVSpace (A.tags + n)) where
  carrier := {t | ∃ i, t ∈ (gammaGroundRVFamilyTagMap i (A.piece i)).image.carrier}
  definable := by
    apply (GammaGroundDefinable.iUnion (fun i => (gammaGroundRVFamilyTagMap i (A.piece i)).image.definable)).congr
    intro t
    simp

def GammaGroundFiniteFamily.rvEncode (A : GammaGroundFiniteFamily hc ground (rawRVSpace (M := M) n)) (a : A.Carrier) : A.rvRealization :=
  ⟨(gammaGroundRVFamilyTagMap a.1 (A.piece a.1) a.2).val, a.1, a.2, rfl⟩

theorem GammaGroundFiniteFamily.rvEncode_bijective (A : GammaGroundFiniteFamily hc ground (rawRVSpace (M := M) n)) :
    Function.Bijective (GammaGroundFiniteFamily.rvEncode A) := by
  constructor
  · rintro ⟨i, a⟩ ⟨j, b⟩ he
    have ht : rvFamilyTag (M := M) i = rvFamilyTag j := by
      funext q
      simpa only [GammaGroundFiniteFamily.rvEncode, gammaGroundRVFamilyTagMap, GammaGroundMap.ofGlobal, rvFamilyTagMap, rvMapOfCode, Map.ofCodes,
        rvAppend, Fin.append_left] using
        congrArg (fun t : A.rvRealization => t.val (Fin.castAdd n q)) he
    have hij := rvFamilyTag_injective ht
    subst j
    have hab : a = b := by
      apply Subtype.ext
      funext q
      simpa only [GammaGroundFiniteFamily.rvEncode, gammaGroundRVFamilyTagMap, GammaGroundMap.ofGlobal, rvFamilyTagMap, rvMapOfCode, Map.ofCodes,
        rvAppend, Fin.append_right] using
        congrArg (fun t : A.rvRealization => t.val (Fin.natAdd A.tags q)) he
    subst b
    rfl
  · intro b
    obtain ⟨i, a, ha⟩ := b.property
    exact ⟨⟨i, a⟩, Subtype.ext ha⟩

def GammaGroundFiniteFamily.rvEquiv (A : GammaGroundFiniteFamily hc ground (rawRVSpace (M := M) n)) : A.Carrier ≃ A.rvRealization :=
  Equiv.ofBijective (GammaGroundFiniteFamily.rvEncode A) (GammaGroundFiniteFamily.rvEncode_bijective A)

end DiamondIntegral.Section3
