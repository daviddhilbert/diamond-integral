import «section 6».MeasuredGoodCoordinatePivots

/-! A good coordinate pivot retains double bounds on the entire original
label domain and on every new volume coordinate. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

theorem rvGoodReplacementObject_doublyBounded {U V : RVObject (M := M) S (n+1)}
    (F : RVHom U V) (j : Fin (n+1)) (E : RawClosure.Tuple.GoodRelation (n := n) S)
    (hU : RVObjectDoublyBounded U) (hV : RVObjectDoublyBounded V) :
    RVObjectDoublyBounded (rvGoodReplacementObject F j E) := by
  constructor
  · obtain ⟨γ,hγ⟩ := hU.1
    exact ⟨γ,fun u hu i => hγ u (rvGoodReplacementDomain_subset F j E hu) i⟩
  · obtain ⟨γ,hγ⟩ := hU.2
    obtain ⟨δ,hδ⟩ := hV.2
    let ε := max γ δ
    have hloγ : (ε⁻¹).val ≤ (γ⁻¹).val := show ε⁻¹ ≤ γ⁻¹ from inv_le_inv' (le_max_left _ _)
    have hloδ : (ε⁻¹).val ≤ (δ⁻¹).val := show ε⁻¹ ≤ δ⁻¹ from inv_le_inv' (le_max_right _ _)
    have hhiγ : γ.val ≤ ε.val := le_max_left _ _
    have hhiδ : δ.val ≤ ε.val := le_max_right _ _
    refine ⟨ε,?_⟩
    rintro t ⟨u,rfl⟩ i
    let a : U.domain := ⟨u.val,rvGoodReplacementDomain_subset F j E u.property⟩
    change (ε⁻¹).val ≤ Values.vrv ((rvLastReplacementMap F j a).val i) ∧
      Values.vrv ((rvLastReplacementMap F j a).val i) ≤ ε.val
    rw [rvLastReplacementMap_value]
    refine Fin.lastCases ?_ (fun k => ?_) i
    · have h := hδ (V.value (F.map a)) ⟨F.map a,rfl⟩ j
      simpa only [Fin.snoc_last] using And.intro (hloδ.trans h.1) (h.2.trans hhiδ)
    · have h := hγ (U.value a) ⟨a,rfl⟩ k.castSucc
      simpa only [Fin.snoc_castSucc,Fin.init] using And.intro (hloγ.trans h.1) (h.2.trans hhiγ)

theorem measuredGoodReplacementObject_doublyBounded (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : MeasuredRVObject (M := M) S (n+1)} (F : RVHom U.object V.object) (j : Fin (n+1))
    (E : RawClosure.Tuple.GoodRelation (n := n) S)
    (hObs : ∀ (t : Fin n → M) (y : M), (t,y) ∉ E.val →
      {x | (Fin.snoc t x,y) ∈ rvCoordinateRelation F j}.Finite)
    (hU : U.doublyBounded) (hV : V.doublyBounded) :
    (measuredGoodReplacementObject hc F j E hObs).doublyBounded :=
  rvGoodReplacementObject_doublyBounded F j E hU hV

end DiamondIntegral.Section6
