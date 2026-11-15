import «section 5».VFPolynomialNativeDomains
import «section 3».GammaGroundMapRestrictions

/-! Actual polynomial coordinate maps between native pure-VF domains
retain their complete original-ground graphs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section5
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {n m : ℕ}

def universalVFPolynomialMap (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) (P : Fin m → MvPolynomial (Fin n) (VFType (M := M)))
    (hcoeff : ∀ i d,((P i).coeff d).val ∈ S) :
    Map (DefSet.univ (rawMixedSpace (M := M) n 0) S) (DefSet.univ (rawMixedSpace m 0) S) := by
  let f (q : Section2.Mixed M n 0) : Section2.Mixed M m 0 := (fun i => MvPolynomial.eval q.1 (P i),Fin.elim0)
  let F (z : Fin n ⊕ Fin 0 → M) : Fin m ⊕ Fin 0 → M := Sum.elim (fun i => mvPolynomialCode (P i) z) Fin.elim0
  have hcode (c : (rawMixedSpace (M := M) n 0).domain) :
      mixedValues (f ((rawMixedSpace n 0).decode c)) = F c.val := by
    funext i
    cases i with
    | inl j =>
      exact (mvPolynomialCode_eq (P j) c.val ((rawMixedSpace n 0).decode c).1
        (fun i => (congrFun (mixedValues_decode c) (.inl i)).symm)).symm
    | inr j => exact j.elim0
  refine Map.ofCodes _ f F (fun i => ?_) (fun c => (hcode c) ▸ mixedValues_mem_domain (f ((rawMixedSpace n 0).decode c))) ?_
  · cases i with
    | inl j =>
      have hp := mvPolynomialCode_definable (m := 0) (P j) (hcoeff j)
      change @Set.DefinableFun M LRV (CanonicalStructure.normalize (M := M)) (Fin n ⊕ Fin 0) S (mvPolynomialCode (m := 0) (P j)) at hp
      rw [canonical_normalize_eq hc] at hp
      exact hp
    | inr j => exact j.elim0
  · intro c
    apply mixedValues_injective
    exact (mixedValues_decode _).trans (hcode c).symm

variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

def nativeVFPolynomialMap (D : GammaGroundDefSet hc B (rawMixedSpace (M := M) n 0))
    (P : Fin m → MvPolynomial (Fin n) (VFType (M := M)))
    (hcoeff : ∀ i d,((P i).coeff d).val ∈ B.real) :
    GammaGroundMap D (GammaGroundDefSet.univ hc B (rawMixedSpace (M := M) m 0)) :=
  GammaGroundMap.ofGlobal D _ (universalVFPolynomialMap hc B.real P hcoeff) (fun _ => Set.mem_univ _)

theorem nativeVFPolynomialMap_value
    (D : GammaGroundDefSet hc B (rawMixedSpace (M := M) n 0))
    (P : Fin m → MvPolynomial (Fin n) (VFType (M := M)))
    (hcoeff : ∀ i d,((P i).coeff d).val ∈ B.real) (a : D) :
    (nativeVFPolynomialMap D P hcoeff a).val = (fun i => MvPolynomial.eval a.val.1 (P i),Fin.elim0) := rfl

end DiamondIntegral.Section5
