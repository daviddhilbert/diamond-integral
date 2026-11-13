import «section 4».Section3GammaRVCodeBridge
import «section 4».Section3GammaFamilyBridge
import «section 4».Section3RVFamilyBridge
import «section 4».FiniteFamilyDomainCongruence
import «section 3».GammaGroundFamilyPieceMaps

/-! Full RV code bijections of finite Gamma families commute with the
actual quotient maps after conversion to chart families. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3

namespace DiamondIntegral.Section4.Section3GammaCodeFamilyBridge
open Section3RVCodeBridge Section3GammaRVCodeBridge GammaRVChartPresentation FiniteFamilyBijections
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

def rvFamily {n : ℕ} (A : GammaGroundGammaObject hc B n) : GammaGroundFiniteFamily hc B (rawRVSpace (M := M) n) :=
  ⟨A.tags, fun i => (gammaGroundGammaRVCodeLift (A.piece i)).domain⟩

def codeFamily {n : ℕ} (A : GammaGroundGammaObject hc B n) : GammaGroundFamilyBijection A.codeLift (rvFamily A) :=
  GammaGroundFamilyBijection.pieces A.codeLift _ (fun i => gammaGroundGammaRVCodeBijection (A.piece i))

def codeEquiv {n : ℕ} (A : GammaGroundGammaObject hc B n) :
    A.codeLift.Carrier ≃ Domain (fun i => sharp (A.piece i).carrier) :=
  (codeFamily A).equiv.trans ((Section3RVFamilyBridge.familyEquiv (rvFamily A)).trans
    (FiniteFamilyDomainCongruence.congr (fun i => rawDomain_codeLift (A.piece i))))

def nativeMap {n m : ℕ} {A : GammaGroundGammaObject hc B n} {D : GammaGroundGammaObject hc B m}
    (F : GammaGroundFamilyBijection A.codeLift D.codeLift) : GammaGroundFamilyBijection (rvFamily A) (rvFamily D) :=
  (codeFamily D).comp (F.comp (codeFamily A).symm)

def liftEquiv {n m : ℕ} {A : GammaGroundGammaObject hc B n} {D : GammaGroundGammaObject hc B m}
    (F : GammaGroundFamilyBijection A.codeLift D.codeLift) :
    Domain (fun i => sharp (A.piece i).carrier) ≃ Domain (fun j => sharp (D.piece j).carrier) :=
  (codeEquiv A).symm.trans (F.equiv.trans (codeEquiv D))

theorem liftEquiv_transport {n m : ℕ} {A : GammaGroundGammaObject hc B n} {D : GammaGroundGammaObject hc B m}
    (F : GammaGroundFamilyBijection A.codeLift D.codeLift) : liftEquiv F =
      FiniteFamilyDomainCongruence.transport (fun i => rawDomain_codeLift (A.piece i))
        (fun j => rawDomain_codeLift (D.piece j)) (Section3RVFamilyBridge.equiv (nativeMap F)) := by
  simp only [liftEquiv, codeEquiv, FiniteFamilyDomainCongruence.transport, Section3RVFamilyBridge.equiv,
    nativeMap, GammaGroundFamilyBijection.comp, GammaGroundFamilyBijection.symm, Equiv.symm_trans, Equiv.trans_assoc]

theorem lift_graph {n m : ℕ} {A : GammaGroundGammaObject hc B n} {D : GammaGroundGammaObject hc B m}
    (F : GammaGroundFamilyBijection A.codeLift D.codeLift) (i : Fin A.tags) (j : Fin D.tags) :
    DefinableOverBase B (fun _ : Fin (m + n) => .rv)
      (RVMeasuredCharts.graphOn (sourcePiece (liftEquiv F) i j) (pieceMap (liftEquiv F) (fun _ => iRVZero) i)) := by
  rw [liftEquiv_transport, FiniteFamilyDomainCongruence.sourcePiece_eq, FiniteFamilyDomainCongruence.pieceMap_eq]
  exact Section3RVFamilyBridge.graph_definable (nativeMap F) i j

theorem decode_commute {n : ℕ} (A : GammaGroundGammaObject hc B n) (c : A.codeLift.Carrier) :
    mapDomain codeValues (fun _ _ h => h.2) (codeEquiv A c) = Section3GammaFamilyBridge.familyEquiv A (A.decode c) :=
  Subtype.ext (Prod.ext rfl (rawCode_value c.2))

theorem contraction {n : ℕ} {A D : GammaGroundGammaObject hc B n} (f : GammaGroundGammaHom A D)
    (F : GammaGroundFamilyBijection A.codeLift D.codeLift)
    (hF : ∀ c, D.decode (F.equiv c) = f.bijection.equiv (A.decode c))
    (p : Domain (fun i => sharp (A.piece i).carrier)) :
    mapDomain codeValues (fun _ _ h => h.2) (liftEquiv F p) =
      Section3GammaFamilyBridge.equiv f.bijection (mapDomain codeValues (fun _ _ h => h.2) p) := by
  obtain ⟨c, rfl⟩ := (codeEquiv A).surjective p
  change mapDomain codeValues (fun _ _ h => h.2)
    (codeEquiv D (F.equiv ((codeEquiv A).symm (codeEquiv A c)))) = _
  rw [Equiv.symm_apply_apply, decode_commute, hF c, decode_commute]
  simp only [Section3GammaFamilyBridge.equiv, Equiv.trans_apply, Equiv.symm_apply_apply]

end DiamondIntegral.Section4.Section3GammaCodeFamilyBridge
