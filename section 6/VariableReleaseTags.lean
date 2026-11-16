import «section 6».RVGammaCutDomains
import «section 6».VariableApertureBundles
import «section 6».CoreBranchImages

/-! Construct the whole-label release locus from an actual old-radius
graph constant on retained RV fibres, without choosing VF coefficients. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}

def rvBooleanTagSet (S : Set M) (j : Fin r) (b : Bool) :
    DefSet (rawRVSpace (M := M) r) S := by
  have h : S.Definable LRV {z : Fin r → M | (branchTag (M := M) b).val=z j} :=
    (branchTag_definable S b).ofPred_eq (Set.DefinableFun.proj LRV)
  refine ⟨{u | u j=branchTag b},?_⟩
  convert rvValues_preimage_definable _ h using 1
  ext u
  exact ⟨fun he => (congrArg Subtype.val he).symm,fun he => Subtype.ext he.symm⟩

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S}
namespace CentripetalData

def regularizedOldLabels (D : CentripetalData (G := G) A) : Fin r → Fin (n+(1+r)) :=
  fun i => Fin.natAdd n (Fin.natAdd 1 i)

theorem regularizedOldLabels_at (D : CentripetalData (G := G) A) (a : Mixed M n r) :
    (regularize (D.point a)).2 ∘ D.regularizedOldLabels=a.2 := by
  funext i
  simp only [regularizedOldLabels,Function.comp_apply,regularize,Fin.append_right,point]

def variableReleaseTags (D : CentripetalData (G := G) A)
    (f : Map (focusActive A D.activeTags) (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hConst : ∀ p q : focusActive A D.activeTags,p.val.2=q.val.2 → (f p).val=(f q).val) :
    DefSet (rawRVSpace (M := M) (n+(1+r))) S := by
  let U := rvGammaCutDomain (gammaFibreValueDescent f hConst) D.regularizedOldLabels
    (Fin.castAdd (1+r) D.coordinate)
  let V := rvBooleanTagSet S (Fin.natAdd n (Fin.castAdd r (0 : Fin 1))) false
  exact ⟨U.carrier ∩ V.carrier,U.definable.inter _ V.definable⟩

theorem variableReleaseTags_at
    (h00 : M ⊨ Axioms.ACVF00) (D : CentripetalData (G := G) A)
    (f : Map (focusActive A D.activeTags) (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hConst : ∀ p q : focusActive A D.activeTags,p.val.2=q.val.2 → (f p).val=(f q).val)
    (a : Mixed M n r) (ha : a ∈ A.carrier) :
    (regularize (D.point a)).2 ∈ (D.variableReleaseTags f hConst).carrier ↔
      a.2 ∈ D.activeTags.carrier ∧
        (gammaFibreValue f a.2).val < vfValue (a.1 D.coordinate-D.extendedFocus a) ∧ D.core a=false := by
  let q := regularize (D.point a)
  have hFlag : q.2 (Fin.natAdd n (Fin.castAdd r (0 : Fin 1)))=branchTag (M := M) (D.core a) :=
    D.regularized_core_flag a
  have hNewTag (hNew : D.core a=false) :
      q.2 (Fin.castAdd (1+r) D.coordinate)=rv M (a.1 D.coordinate-D.extendedFocus a) := by
    simp only [q,regularize,Fin.append_left,point,Function.update_self,hNew,
      Bool.false_eq_true,ite_false,add_zero]
    change rv M (Function.update a.1 D.coordinate
      (a.1 D.coordinate-D.extendedFocus a) D.coordinate)=_
    rw [Function.update_self]
  constructor
  · rintro ⟨hCut,hFalse⟩
    change q.2 (Fin.natAdd n (Fin.castAdd r (0 : Fin 1)))=branchTag false at hFalse
    have hNew : D.core a=false := branchTag_injective h00 (hFlag.symm.trans hFalse)
    obtain ⟨b,hb,hBound⟩ := (mem_rvGammaCutDomain _ _ _ q.2).mp hCut
    have hbTags : b.val=a.2 := hb.trans (D.regularizedOldLabels_at a)
    obtain ⟨p,hp⟩ := b.property
    have hu : a.2 ∈ D.activeTags.carrier := by
      have hTags : p.val.2=a.2 := hp.trans hbTags
      exact hTags ▸ p.property.2
    let aActive : focusActive A D.activeTags := ⟨a,ha,hu⟩
    have hbEq : b=pureRVTagQuotient (focusActive A D.activeTags) aActive := Subtype.ext hbTags
    rw [hbEq,gammaFibreValueDescent_at,hNewTag hNew] at hBound
    exact ⟨hu,hBound,hNew⟩
  · rintro ⟨hu,hBound,hNew⟩
    let aActive : focusActive A D.activeTags := ⟨a,ha,hu⟩
    refine ⟨(mem_rvGammaCutDomain _ _ _ q.2).mpr ?_,?_⟩
    · refine ⟨pureRVTagQuotient (focusActive A D.activeTags) aActive,
        (D.regularizedOldLabels_at a).symm,?_⟩
      rw [gammaFibreValueDescent_at,hNewTag hNew]
      exact hBound
    · change q.2 (Fin.natAdd n (Fin.castAdd r (0 : Fin 1)))=branchTag false
      rw [hFlag,hNew]

theorem variableReleaseData_of_gamma_graph
    (h00 : M ⊨ Axioms.ACVF00) (D : CentripetalData (G := G) A)
    (f : Map (focusActive A D.activeTags) (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hConst : ∀ p q : focusActive A D.activeTags,p.val.2=q.val.2 → (f p).val=(f q).val)
    (hStable : ∀ a ∈ A.carrier,a.2 ∈ D.activeTags.carrier → ∀ x : VF M,
      (gammaFibreValue f a.2).val < vfValue (a.1 D.coordinate-x) →
        (Function.update a.1 D.coordinate x,a.2) ∈ A.carrier) :
    VariableApertureReleaseData D (D.variableReleaseTags f hConst) (gammaFibreValue f) :=
  ⟨D.variableReleaseTags_at h00 f hConst,hStable⟩

end CentripetalData
end DiamondIntegral.Section6
