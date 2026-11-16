import «section 6».RegularizedBundleBaseGeometry

/-! Full regularization preserves the carried-coordinate bundle,
with the new leading-term coordinate as its label. The next actual
lower-dimensional component therefore lifts to this precise source,
without suppressing or renaming away the extra regularization tag. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}

theorem regularizedBundle_full_set
    (A : DefSet (rawMixedSpace (M := M) n r) S) (k : Fin r) :
    (regularizeMap (rvCoordinateBundle A k)).image.carrier =
      (rvCoordinateBundle (regularizedBundleBase A k) (Fin.castAdd r (Fin.last n))).carrier := by
  ext p
  constructor
  · intro hp
    refine ⟨⟨⟨p,hp⟩,rfl⟩,?_⟩
    have hpf : p.1 ∈ vfFibre (regularizeMap (rvCoordinateBundle A k)).image.carrier p.2 := hp
    rw [regularization_carrier,regularized_fibre] at hpf
    exact congrFun hpf.2 (Fin.last n)
  · intro hp
    have hBase : Fin.init p.1 ∈ vfFibre (regularizedBundleBase A k).carrier p.2 := hp.1
    have hTag : p.2 (Fin.castAdd r (Fin.last n)) = p.2 (Fin.natAdd (n+1) k) := by
      by_contra hn
      rw [regularizedBundleBase_fibre,if_neg hn] at hBase
      exact hBase
    rw [regularizedBundleBase_fibre,if_pos hTag] at hBase
    rw [regularization_carrier,regularized_fibre,regularizedBundleLabels_old,
      regularizedBundleLabels_new] at hBase
    change p.1 ∈ vfFibre (regularizeMap (rvCoordinateBundle A k)).image.carrier p.2
    rw [regularization_carrier,regularized_fibre]
    refine ⟨⟨hBase.1,?_⟩,?_⟩
    · exact hp.2.trans hTag
    · funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact hp.2
      · exact congrFun hBase.2 j

theorem regularizedBundle_defSet_eq
    (A : DefSet (rawMixedSpace (M := M) n r) S) (k : Fin r) :
    rvCoordinateBundle (regularizedBundleBase A k) (Fin.castAdd r (Fin.last n)) =
      (regularizeMap (rvCoordinateBundle A k)).image :=
  defSet_eq_of_carrier_eq (regularizedBundle_full_set A k).symm

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

def CentripetalData.carryThroughRegularization
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : DefSet (rawMixedSpace (M := M) n r) S) (k : Fin r)
    (hA : ProperInvariant S A.carrier) (hDouble : VFDoublyBounded A.carrier)
    (D : CentripetalData (G := G) (regularizeMap A).image) :
    CentripetalData (G := G) (regularizeMap (rvCoordinateBundle A k)).image := by
  let C := regularizedBundleBase A k
  have hC : ProperInvariant S C.carrier := regularizedBundleBase_properInvariant h00 hc hκ hs hv A k hA hDouble
  let D' := D.afterBundleRegularization h00 hc hκ hs hv A k hA hDouble
  let E := D'.carryCoordinate (Fin.castAdd r (Fin.last n))
    (rvCoordinateBundle_properInvariant h00 hc hκ hs hv C (Fin.castAdd r (Fin.last n)) hC)
  exact regularizedBundle_defSet_eq A k ▸ E

end DiamondIntegral.Section6
