import «section 6».UnaryRootFoci
import «section 6».MixedVFProjectionMaps
import «section 6».FiniteCenterSeparation
import «section 6».NamedVFValues

/-! Finite global VF values of an actual unary root family. All centers
and barycenters are kept as definable families over the original base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.UnaryRootFamily
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}

def fieldValues (R : UnaryRootFamily A) : Set (VF M) := scalarFocusImage (mixedVFHeadMap R.roots)

theorem fieldValues_definable (R : UnaryRootFamily A) :
    S.Definable₁ LRV (Subtype.val '' R.fieldValues) := scalarFocusImage_definable _

theorem fieldValues_finite (R : UnaryRootFamily A)
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal} (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ) : R.fieldValues.Finite := by
  have hsort (t : Fin r → M) (y : Fin 1 → M)
      (hy : (t,y 0) ∈ Barycentre.finiteFibreRelation R.rawFamily) :
      (∀ i, iRV (t i)) ∧ ∀ i, iVF (y i) := by
    obtain ⟨x,hx,he⟩ := hy
    have ht : ∀ i, iRV (t i) := by
      by_contra hn
      have hh : R.rawFamily t = ∅ := dif_neg hn
      exact Finset.notMem_empty _ (hh ▸ hx)
    refine ⟨ht,?_⟩
    intro i
    fin_cases i
    have he' : x.val = y 0 := he
    change iVF (y 0)
    rw [← he']
    exact x.property
  have hf (t : Fin r → M) :
      {y : Fin 1 → M | (t,y 0) ∈ Barycentre.finiteFibreRelation R.rawFamily}.Finite := by
    apply ((R.rawFamily t).finite_toSet.image (fun x => fun _ : Fin 1 => x.val)).subset
    rintro y ⟨x,hx,he⟩
    exact ⟨x,hx,by funext i; fin_cases i; exact he⟩
  have hfin := finite_rv_to_vf_tuple_relation_image hc hs S hsmall _ R.rawFamily_definable hsort hf
  have hi : Function.Injective (fun x : VF M => fun _ : Fin 1 => x.val) := by
    intro x y he
    exact Subtype.ext (congrFun he 0)
  apply (hfin.preimage hi.injOn).subset
  rintro x ⟨p,rfl⟩
  refine ⟨rvValues p.val.2,p.val.1 0,?_,rfl⟩
  change p.val.1 0 ∈ R.rawFamily (rvValues p.val.2)
  rw [R.rawFamily_labels,R.mem_fibre]
  have hEta : (fun _ : Fin 1 => p.val.1 0)=p.val.1 := by funext i; fin_cases i; rfl
  simpa only [hEta,Prod.eta] using p.property

end DiamondIntegral.Section6.UnaryRootFamily
