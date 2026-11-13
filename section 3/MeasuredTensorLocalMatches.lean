import «section 3».MeasuredTensorBoxValues
import «section 3».TensorLocalMatchReversal
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {r n : ℕ}
variable {P Q : Space LRV M} {U0 : GammaGroundDefSet hc B P} {V0 : GammaGroundDefSet hc B Q}

/-- A weighted product match keeps the actual underlying RV map and
the measured positive congruence of its two prescribed-weight boxes. -/
structure GammaGroundMeasuredTensorBoxMatch (F : GammaGroundBijection U0 V0)
    (X : GammaGroundRESUnitChart hc B r) (G : GammaGroundGammaPiece hc B n)
    (a : GammaGroundMap (gammaGroundNativeProductDomain X G) U0)
    (f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hf : FullGammaFunction (integrationGammaBase B) f)
    (Y : GammaGroundRESUnitChart hc B r) (H : GammaGroundGammaPiece hc B n)
    (b : GammaGroundMap (gammaGroundNativeProductDomain Y H) V0)
    (g : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hg : FullGammaFunction (integrationGammaBase B) g)
    (L : GammaGroundTensorBox X G) (R : GammaGroundTensorBox Y H) where
  data : GammaGroundTensorBoxMatch F X G a Y H b L R
  congruence : gammaGroundMeasuredCoefficientCongruence (L.measuredValue f hf) (R.measuredValue g hg)

namespace GammaGroundMeasuredTensorBoxMatch
variable {F : GammaGroundBijection U0 V0}
variable {X Y : GammaGroundRESUnitChart hc B r} {G H : GammaGroundGammaPiece hc B n}
variable {a : GammaGroundMap (gammaGroundNativeProductDomain X G) U0}
variable {b : GammaGroundMap (gammaGroundNativeProductDomain Y H) V0}
variable {f g : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)}
variable {hf : FullGammaFunction (integrationGammaBase B) f} {hg : FullGammaFunction (integrationGammaBase B) g}
variable {L : GammaGroundTensorBox X G} {R : GammaGroundTensorBox Y H}

def symm (E : GammaGroundMeasuredTensorBoxMatch F X G a f hf Y H b g hg L R) :
    GammaGroundMeasuredTensorBoxMatch F.symm Y H b g hg X G a f hf R L :=
  ⟨E.data.symm,gammaGroundMeasuredCoefficientCongruence.symm E.congruence⟩

def unsymm (F : GammaGroundBijection U0 V0)
    (E : GammaGroundMeasuredTensorBoxMatch F.symm Y H b g hg X G a f hf R L) :
    GammaGroundMeasuredTensorBoxMatch F X G a f hf Y H b g hg L R :=
  ⟨E.data.unsymm F,gammaGroundMeasuredCoefficientCongruence.symm E.congruence⟩
end GammaGroundMeasuredTensorBoxMatch

/-- Two-sided weighted cuts retain their measured congruence after any
nonempty product restriction. The original weights are not re-chosen. -/
structure GammaGroundMeasuredTensorLocalMatch (F : GammaGroundBijection U0 V0)
    (X : GammaGroundRESUnitChart hc B r) (G : GammaGroundGammaPiece hc B n)
    (a : GammaGroundMap (gammaGroundNativeProductDomain X G) U0)
    (f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hf : FullGammaFunction (integrationGammaBase B) f)
    (Y : GammaGroundRESUnitChart hc B r) (H : GammaGroundGammaPiece hc B n)
    (b : GammaGroundMap (gammaGroundNativeProductDomain Y H) V0)
    (g : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hg : FullGammaFunction (integrationGammaBase B) g) where
  source : GammaGroundTensorBox X G
  target : GammaGroundTensorBox Y H
  data : GammaGroundMeasuredTensorBoxMatch F X G a f hf Y H b g hg source target
  sourceCuts : ∀ L : GammaGroundTensorBox X G,
    L.residue.carrier ⊆ source.residue.carrier → L.gamma.carrier ⊆ source.gamma.carrier →
    L.residue.carrier.Nonempty → L.gamma.carrier.Nonempty →
      ∃ R : GammaGroundTensorBox Y H, Nonempty (GammaGroundMeasuredTensorBoxMatch F X G a f hf Y H b g hg L R)
  targetCuts : ∀ R : GammaGroundTensorBox Y H,
    R.residue.carrier ⊆ target.residue.carrier → R.gamma.carrier ⊆ target.gamma.carrier →
    R.residue.carrier.Nonempty → R.gamma.carrier.Nonempty →
      ∃ L : GammaGroundTensorBox X G, Nonempty (GammaGroundMeasuredTensorBoxMatch F X G a f hf Y H b g hg L R)

namespace GammaGroundMeasuredTensorLocalMatch
variable {F : GammaGroundBijection U0 V0}
variable {X Y : GammaGroundRESUnitChart hc B r} {G H : GammaGroundGammaPiece hc B n}
variable {a : GammaGroundMap (gammaGroundNativeProductDomain X G) U0}
variable {b : GammaGroundMap (gammaGroundNativeProductDomain Y H) V0}
variable {f g : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)}
variable {hf : FullGammaFunction (integrationGammaBase B) f} {hg : FullGammaFunction (integrationGammaBase B) g}

def forget (E : GammaGroundMeasuredTensorLocalMatch F X G a f hf Y H b g hg) :
    GammaGroundTensorLocalMatch F X G a Y H b where
  source := E.source
  target := E.target
  data := E.data.data
  sourceCuts := by
    intro L hA hG hneA hneG
    obtain ⟨R,⟨d⟩⟩ := E.sourceCuts L hA hG hneA hneG
    exact ⟨R,⟨d.data⟩⟩
  targetCuts := by
    intro R hA hG hneA hneG
    obtain ⟨L,⟨d⟩⟩ := E.targetCuts R hA hG hneA hneG
    exact ⟨L,⟨d.data⟩⟩

def symm (E : GammaGroundMeasuredTensorLocalMatch F X G a f hf Y H b g hg) :
    GammaGroundMeasuredTensorLocalMatch F.symm Y H b g hg X G a f hf where
  source := E.target
  target := E.source
  data := E.data.symm
  sourceCuts := by
    intro L hA hG hneA hneG
    obtain ⟨R,⟨d⟩⟩ := E.targetCuts L hA hG hneA hneG
    exact ⟨R,⟨d.symm⟩⟩
  targetCuts := by
    intro R hA hG hneA hneG
    obtain ⟨L,⟨d⟩⟩ := E.sourceCuts R hA hG hneA hneG
    exact ⟨L,⟨d.symm⟩⟩

def unsymm (F : GammaGroundBijection U0 V0)
    (E : GammaGroundMeasuredTensorLocalMatch F.symm Y H b g hg X G a f hf) :
    GammaGroundMeasuredTensorLocalMatch F X G a f hf Y H b g hg where
  source := E.target
  target := E.source
  data := E.data.unsymm F
  sourceCuts := by
    intro L hA hG hneA hneG
    obtain ⟨R,⟨d⟩⟩ := E.targetCuts L hA hG hneA hneG
    exact ⟨R,⟨d.unsymm F⟩⟩
  targetCuts := by
    intro R hA hG hneA hneG
    obtain ⟨L,⟨d⟩⟩ := E.sourceCuts R hA hG hneA hneG
    exact ⟨L,⟨d.unsymm F⟩⟩
end GammaGroundMeasuredTensorLocalMatch
end DiamondIntegral.Section3
