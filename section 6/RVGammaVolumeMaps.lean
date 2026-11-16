import «section 6».TupleCoordinateMaps

/-! Actual Gamma volume maps in every RV degree. Finite products are
constructed from the checked Gamma arithmetic maps over the original base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

def gammaMapProduct {P : SpecialTransformations.DefinableGeometry.Space LRV M}
    (hc : CanonicalStructure.IsCanonical (M := M)) (A : DefSet P S) :
    (n : ℕ) → (Fin n → Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) →
      Map A (DefSet.univ (rawGammaPresentation (M := M)) S)
  | 0,_ => gammaOneMap hc A
  | n+1,F => gammaMapMul hc (F 0) (gammaMapProduct hc A n (fun i => F i.succ))

theorem gammaMapProduct_value {P : SpecialTransformations.DefinableGeometry.Space LRV M}
    (hc : CanonicalStructure.IsCanonical (M := M)) (A : DefSet P S) (n : ℕ)
    (F : Fin n → Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) (a : A) :
    gammaMapValue (gammaMapProduct hc A n F) a = ∏ i, gammaMapValue (F i) a := by
  induction n with
  | zero => simp only [gammaMapProduct,gammaOneMap_value,Finset.univ_eq_empty,Finset.prod_empty]
  | succ n ih =>
    change gammaMapValue (F 0) a * gammaMapValue (gammaMapProduct hc A n (fun i => F i.succ)) a = _
    rw [ih,Fin.prod_univ_succ]

def rvCoordinateGammaMap {n : ℕ} (U : RVObject (M := M) S n) (i : Fin n) :=
  (scalarRVGammaMap S).comp ((rvTupleSelectMap S (fun _ : Fin 1 => i)).comp U.volume)

theorem rvCoordinateGammaMap_value {n : ℕ} (U : RVObject (M := M) S n)
    (hnz : ∀ u, ∀ i, (U.value u i).val ≠ iRVZero) (u : U.domain) (i : Fin n) :
    gammaMapValue (rvCoordinateGammaMap U i) u = Values.gammaOf (U.value u i) (hnz u i) := by
  apply Subtype.ext
  change (gammaMapValue (scalarRVGammaMap S)
    ((rvTupleSelectMap S (fun _ : Fin 1 => i)).comp U.volume u)).val = _
  rw [scalarRVGammaMap_nonzero S _ (hnz u i)]
  rfl

def rvVolumeGammaMap {n : ℕ} (hc : CanonicalStructure.IsCanonical (M := M)) (U : RVObject (M := M) S n) :=
  gammaMapProduct hc U.domain n (rvCoordinateGammaMap U)

theorem rvVolumeGammaMap_value {n : ℕ} (hc : CanonicalStructure.IsCanonical (M := M))
    (U : RVObject (M := M) S n) (hnz : ∀ u, ∀ i, (U.value u i).val ≠ iRVZero) (u : U.domain) :
    gammaMapValue (rvVolumeGammaMap hc U) u = rvVolumeGamma (U.value u) (hnz u) := by
  change gammaMapValue (gammaMapProduct hc U.domain n (rvCoordinateGammaMap U)) u = _
  rw [gammaMapProduct_value]
  exact Finset.prod_congr rfl (fun i hi => rvCoordinateGammaMap_value U hnz u i)

end DiamondIntegral.Section6
