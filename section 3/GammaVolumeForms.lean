import Section8.GammaRadiusBase
import Section4.Spaces

/-! Gamma volume forms use the complete imaginary presentation, so their
maps have invariant graphs over the original base, including every RV code. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8

noncomputable section
namespace DiamondIntegral.Section3
/-- Change only the proof of definability, keeping the presentation's
carrier, real codes and decoding function literally unchanged. -/
def rebaseSpace {L : Language} {M : Type} {s t : L.Structure M}
    (h : s = t) (P : @Space L M s) : @Space L M t where
  Carrier := @Space.Carrier L M s P
  Index := @Space.Index L M s P
  finiteIndex := @Space.finiteIndex L M s P
  domain := @Space.domain L M s P
  domain_definable := by cases h; exact @Space.domain_definable L M s P
  decode := @Space.decode L M s P
  onto := @Space.onto L M s P
  diagonal_definable := by cases h; exact @Space.diagonal_definable L M s P

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M}

/-- The existing imaginary Gamma presentation with its original actual
Gamma carrier and every nonzero RV representative. Only the definability
proof is rebased from the normalization of a canonical structure. -/
def volumeGammaSpace (hc : CanonicalStructure.IsCanonical (M := M)) : Space LRV M :=
  rebaseSpace (normalize_eq_of_isCanonical hc) (@gammaSpace M sM hM)

theorem gammaCarrier (hc : CanonicalStructure.IsCanonical (M := M)) :
    (volumeGammaSpace hc).Carrier = Values.Gamma (M := M) := rfl

/-- A definable map into the actual Gamma imaginary, using all its RV
codes in the graph presentation. -/
abbrev GammaVolumeForm (hc : CanonicalStructure.IsCanonical (M := M))
    {P : Space LRV M} (A : DefSet P S) := Map A (DefSet.univ (volumeGammaSpace hc) S)

def gammaFormValue {hc : CanonicalStructure.IsCanonical (M := M)}
    {P : Space LRV M} {A : DefSet P S} (ω : GammaVolumeForm hc A) (p : A) :
    Values.Gamma (M := M) :=
  cast (gammaCarrier hc) (ω p).val


end DiamondIntegral.Section3
