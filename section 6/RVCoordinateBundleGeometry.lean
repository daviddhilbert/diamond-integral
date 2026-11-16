import «section 6».RVCoordinateBundles

/-! Exact projection, double bounds, taggedness and RV-pullback
geometry of an actual carried-coordinate bundle. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}

def bundleProjection (C : DefSet (rawMixedSpace (M := M) n r) S) (k : Fin r) :
    Map (rvCoordinateBundle C k) C :=
  (vfDropLast (rvCoordinateBundle C k)).corestrict (fun p => p.property.1)

theorem bundleProjection_surjective (C : DefSet (rawMixedSpace (M := M) n r) S) (k : Fin r) :
    Function.Surjective (bundleProjection C k) := by
  intro p
  obtain ⟨x,hx⟩ := rv_surjective (p.val.2 k)
  let q : Mixed M (n+1) r := (Fin.snoc p.val.1 x,p.val.2)
  have hinit : Fin.init q.1 = p.val.1 := by simp only [q,Fin.init_snoc]
  have hbase : ((Fin.init q.1,q.2) : Mixed M n r) = p.val := Prod.ext hinit rfl
  have hq : q ∈ (rvCoordinateBundle C k).carrier := by
    refine ⟨?_,?_⟩
    · exact hbase.symm ▸ p.property
    · simpa only [q,Fin.snoc_last] using hx
  refine ⟨⟨q,hq⟩,?_⟩
  apply Subtype.ext
  exact hbase

theorem rvCoordinateBundle_doublyBounded (C : DefSet (rawMixedSpace (M := M) n r) S) (k : Fin r)
    (hC : VFDoublyBounded C.carrier) (hRV : RVSupportDoublyBounded C.carrier) :
    VFDoublyBounded (rvCoordinateBundle C k).carrier := by
  obtain ⟨γ,hγ⟩ := hC
  obtain ⟨δ,hδ⟩ := hRV
  refine ⟨max γ δ,fun p hp i => ?_⟩
  have hloγ : ((max γ δ)⁻¹).val ≤ (γ⁻¹).val := inv_le_inv' (le_max_left γ δ)
  have hloδ : ((max γ δ)⁻¹).val ≤ (δ⁻¹).val := inv_le_inv' (le_max_right γ δ)
  have hhiγ : γ.val ≤ (max γ δ).val := le_max_left γ δ
  have hhiδ : δ.val ≤ (max γ δ).val := le_max_right γ δ
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have he : vfValue (p.1 (Fin.last n)) = Values.vrv (p.2 k) := congrArg Values.vrv hp.2
    rw [he]
    exact ⟨hloδ.trans (hδ (Fin.init p.1,p.2) hp.1 k).1,(hδ (Fin.init p.1,p.2) hp.1 k).2.trans hhiδ⟩
  · exact ⟨hloγ.trans (hγ (Fin.init p.1,p.2) hp.1 j).1,(hγ (Fin.init p.1,p.2) hp.1 j).2.trans hhiγ⟩

theorem rvCoordinateBundle_pullback (C : DefSet (rawMixedSpace (M := M) n r) S) (k : Fin r)
    (hC : IsRVPullback C.carrier) : IsRVPullback (rvCoordinateBundle C k).carrier := by
  apply Set.Subset.antisymm
  · intro p hp
    obtain ⟨q,hq,hrv,htags⟩ := (mem_rvHull_iff _ p).mp hp
    refine ⟨?_,?_⟩
    · have hbase : (Fin.init p.1,p.2) ∈ rvHull C.carrier := by
        apply (mem_rvHull_iff _ _).mpr
        refine ⟨(Fin.init q.1,q.2),hq.1,?_,htags⟩
        funext i
        exact congrFun hrv i.castSucc
      rwa [hC] at hbase
    · exact (congrFun hrv (Fin.last n)).symm.trans (hq.2.trans (congrFun htags k))
  · exact subset_rvHull _

theorem rvCoordinateBundle_tagged (C : DefSet (rawMixedSpace (M := M) n r) S) (k : Fin r)
    (hC : ∀ p ∈ C.carrier, ∀ q ∈ C.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1) :
    ∀ p ∈ (rvCoordinateBundle C k).carrier, ∀ q ∈ (rvCoordinateBundle C k).carrier,
      p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1 := by
  intro p hp q hq htags
  have hbase := hC (Fin.init p.1,p.2) hp.1 (Fin.init q.1,q.2) hq.1 htags
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact hp.2.trans ((congrFun htags k).trans hq.2.symm)
  · exact congrFun hbase j

end DiamondIntegral.Section6
