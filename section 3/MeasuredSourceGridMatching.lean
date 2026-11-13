import «section 3».MeasuredTensorLocalMatches
import «section 3».SourceGridMatching
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {r n N : ℕ}
variable {P Q : Space LRV M} {U0 : GammaGroundDefSet hc B P} {V0 : GammaGroundDefSet hc B Q}

structure GammaGroundMeasuredTensorSourceGridMatching (F : GammaGroundBijection U0 V0)
    (X : GammaGroundRESUnitChart hc B r) (G : GammaGroundGammaPiece hc B n)
    (a : GammaGroundMap (gammaGroundNativeProductDomain X G) U0)
    (u : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hu : FullGammaFunction (integrationGammaBase B) u)
    (Y : Fin N → GammaGroundRESUnitChart hc B r) (H : Fin N → GammaGroundGammaPiece hc B n)
    (b : ∀ i, GammaGroundMap (gammaGroundNativeProductDomain (Y i) (H i)) V0)
    (v : Fin N → (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hv : ∀ i, FullGammaFunction (integrationGammaBase B) (v i))
    (E : ∀ i, GammaGroundMeasuredTensorLocalMatch F X G a u hu (Y i) (H i) (b i) (v i) (hv i)) where
  targetIndex : GammaGroundTensorGridCoveredIndex X G (fun i => (E i).source.residue) (fun i => (E i).source.gamma) → Fin N
  target : ∀ c, GammaGroundTensorBox (Y (targetIndex c)) (H (targetIndex c))
  data : ∀ c, GammaGroundMeasuredTensorBoxMatch F X G a u hu (Y (targetIndex c)) (H (targetIndex c)) (b (targetIndex c))
    (v (targetIndex c)) (hv (targetIndex c))
    (gammaGroundTensorGridBox X G (fun i => (E i).source.residue) (fun i => (E i).source.gamma) c.val) (target c)

def gammaGroundMeasuredTensorSourceGridMatching (F : GammaGroundBijection U0 V0)
    (X : GammaGroundRESUnitChart hc B r) (G : GammaGroundGammaPiece hc B n)
    (a : GammaGroundMap (gammaGroundNativeProductDomain X G) U0)
    (u : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hu : FullGammaFunction (integrationGammaBase B) u)
    (Y : Fin N → GammaGroundRESUnitChart hc B r) (H : Fin N → GammaGroundGammaPiece hc B n)
    (b : ∀ i, GammaGroundMap (gammaGroundNativeProductDomain (Y i) (H i)) V0)
    (v : Fin N → (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hv : ∀ i, FullGammaFunction (integrationGammaBase B) (v i))
    (E : ∀ i, GammaGroundMeasuredTensorLocalMatch F X G a u hu (Y i) (H i) (b i) (v i) (hv i)) :
    GammaGroundMeasuredTensorSourceGridMatching F X G a u hu Y H b v hv E := by
  let A := fun i => (E i).source.residue
  let K := fun i => (E i).source.gamma
  let I := GammaGroundTensorGridCoveredIndex X G A K
  let index : I → Fin N := fun c => Classical.choose c.property.2
  have hindex (c : I) : c.val.1 (index c) = true ∧ c.val.2 (index c) = true := Classical.choose_spec c.property.2
  have hcut (c : I) : ∃ R : GammaGroundTensorBox (Y (index c)) (H (index c)),
      Nonempty (GammaGroundMeasuredTensorBoxMatch F X G a u hu (Y (index c)) (H (index c)) (b (index c))
        (v (index c)) (hv (index c)) (gammaGroundTensorGridBox X G A K c.val) R) := by
    obtain ⟨hA,hK⟩ := gammaGroundTensorGridBox_factors_subset X G A K c.val (index c) (hindex c)
    exact (E (index c)).sourceCuts _ hA hK c.property.1.1 c.property.1.2
  choose R hR using hcut
  exact ⟨index,R,fun c => Classical.choice (hR c)⟩

namespace GammaGroundMeasuredTensorSourceGridMatching
variable {F : GammaGroundBijection U0 V0}
variable {X : GammaGroundRESUnitChart hc B r} {G : GammaGroundGammaPiece hc B n}
variable {a : GammaGroundMap (gammaGroundNativeProductDomain X G) U0}
variable {u : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)} {hu : FullGammaFunction (integrationGammaBase B) u}
variable {Y : Fin N → GammaGroundRESUnitChart hc B r} {H : Fin N → GammaGroundGammaPiece hc B n}
variable {b : ∀ i, GammaGroundMap (gammaGroundNativeProductDomain (Y i) (H i)) V0}
variable {v : Fin N → (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)}
variable {hv : ∀ i, FullGammaFunction (integrationGammaBase B) (v i)}
variable {E : ∀ i, GammaGroundMeasuredTensorLocalMatch F X G a u hu (Y i) (H i) (b i) (v i) (hv i)}

abbrev Cell := GammaGroundTensorGridCoveredIndex X G (fun i => (E i).source.residue) (fun i => (E i).source.gamma)

def forget (R : GammaGroundMeasuredTensorSourceGridMatching F X G a u hu Y H b v hv E) :
    GammaGroundTensorSourceGridMatching F X G a Y H b (fun i => (E i).forget) :=
  ⟨R.targetIndex,R.target,fun c => (R.data c).data⟩

theorem congruence (R : GammaGroundMeasuredTensorSourceGridMatching F X G a u hu Y H b v hv E) :
    gammaGroundMeasuredCoefficientCongruence
      (∑ c : Cell (E := E), (gammaGroundTensorGridBox X G (fun i => (E i).source.residue) (fun i => (E i).source.gamma) c.val).measuredValue u hu)
      (∑ c : Cell (E := E), (R.target c).measuredValue (v (R.targetIndex c)) (hv (R.targetIndex c))) :=
  gammaGroundMeasuredCoefficientCongruence.finsetSum Finset.univ (fun c _ => (R.data c).congruence)
end GammaGroundMeasuredTensorSourceGridMatching
end DiamondIntegral.Section3
