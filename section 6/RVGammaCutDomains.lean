import «section 6».PureRVDiscQuotients
import «section 6».GammaFibreValueChoice
import «section 6».RVLabelSelection

/-! Definable RV-label loci above a Gamma-valued old aperture.
The complete Gamma graph retains all representatives of each radius. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r s : ℕ}

def rvGammaCutCodes {B : DefSet (rawRVSpace (M := M) r) S}
    (f : Map B (DefSet.univ (rawGammaPresentation (M := M)) S))
    (π : Fin r → Fin s) (j : Fin s) : Set (Fin s → M) :=
  {z | ∃ t : Fin 1 → M,
    Sum.elim (z ∘ π) t ∈ (rawRVSpace r).relation (rawGammaPresentation (M := M))
      (fun x y => ∃ b : B,b.val=x ∧ (f b).val=y) ∧ ¬ iLe (z j) (t 0)}

theorem rvGammaCutCodes_definable {B : DefSet (rawRVSpace (M := M) r) S}
    (f : Map B (DefSet.univ (rawGammaPresentation (M := M)) S))
    (π : Fin r → Fin s) (j : Fin s) : S.Definable LRV (rvGammaCutCodes f π j) := by
  let idx : Fin r ⊕ Fin 1 → Fin s ⊕ Fin 1 := Sum.elim (fun i => .inl (π i)) Sum.inr
  have hGraph := f.graph_definable.preimage_comp idx
  have hLe : S.Definable LRV {z : Fin s ⊕ Fin 1 → M | iLe (z (.inl j)) (z (.inr 0))} :=
    rvCode_compare_definable (Set.DefinableFun.proj LRV) (Set.DefinableFun.proj LRV)
  convert (hGraph.inter hLe.compl).exists_of_finite using 1
  ext z
  change (∃ t, _ ∧ _) ↔ ∃ t, _ ∧ _
  apply exists_congr
  intro t
  have he : Sum.elim z t ∘ idx=Sum.elim (z ∘ π) t := by
    funext i
    cases i <;> rfl
  change (_ ∧ _) ↔ ((Sum.elim z t ∘ idx) ∈
    (rawRVSpace r).relation (rawGammaPresentation (M := M))
      (fun x y => ∃ b : B,b.val=x ∧ (f b).val=y) ∧ ¬ iLe (z j) (t 0))
  rw [he]

def rvGammaCutDomain {B : DefSet (rawRVSpace (M := M) r) S}
    (f : Map B (DefSet.univ (rawGammaPresentation (M := M)) S))
    (π : Fin r → Fin s) (j : Fin s) : DefSet (rawRVSpace (M := M) s) S :=
  ⟨{u | rvValues u ∈ rvGammaCutCodes f π j},
    rvValues_preimage_definable _ (rvGammaCutCodes_definable f π j)⟩

theorem mem_rvGammaCutDomain {B : DefSet (rawRVSpace (M := M) r) S}
    (f : Map B (DefSet.univ (rawGammaPresentation (M := M)) S))
    (π : Fin r → Fin s) (j : Fin s) (u : Fin s → RVInfinity M) :
    u ∈ (rvGammaCutDomain f π j).carrier ↔
      ∃ b : B,b.val=u ∘ π ∧ (f b).val.val < Values.vrv (u j) := by
  constructor
  · rintro ⟨t,⟨hDom,hGamma,b,hb,hf⟩,hCompare⟩
    have hDecoded : (rawRVSpace (M := M) r).decode ⟨rvValues u ∘ π,hDom⟩=u ∘ π := by
      apply rvValues_injective
      exact (SpecialTransformations.Section4.rvValues_decode _).trans rfl
    have hb' : b.val=u ∘ π := hb.trans hDecoded
    let tRV : RVInfinity M := ⟨t 0,hGamma.1⟩
    have hNZ : tRV ≠ rvZero M := fun h => hGamma.2 (congrArg Subtype.val h)
    have hValue : (GammaParameters.codeValue (t 0)).val=Values.vrv tRV :=
      nonzero_rv_codeValue_val tRV hNZ
    change (f b).val=GammaParameters.codeValue (t 0) at hf
    refine ⟨b,hb',?_⟩
    rw [hf,hValue]
    apply lt_of_not_ge
    intro hLe
    exact hCompare ((Values.vrv_le_iff (u j) tRV).mp hLe)
  · rintro ⟨b,hb,hCut⟩
    obtain ⟨t,ht,hValueAt⟩ := GammaParameters.EndpointLogic.codeValue_surjective (f b).val
    let tCode : Fin 1 → M := fun _ => t
    have hDom : rvValues u ∘ π ∈ (rawRVSpace (M := M) r).domain := by
      change rvValues (u ∘ π) ∈ (rawRVSpace (M := M) r).domain
      exact ⟨u ∘ π,rfl⟩
    have hDecoded : (rawRVSpace (M := M) r).decode ⟨rvValues u ∘ π,hDom⟩=u ∘ π := by
      apply rvValues_injective
      exact (SpecialTransformations.Section4.rvValues_decode _).trans rfl
    refine ⟨tCode,⟨hDom,ht,b,hb.trans hDecoded.symm,hValueAt.symm⟩,?_⟩
    let tRV : RVInfinity M := ⟨t,ht.1⟩
    have hNZ : tRV ≠ rvZero M := fun h => ht.2 (congrArg Subtype.val h)
    have hValue : (GammaParameters.codeValue t).val=Values.vrv tRV :=
      nonzero_rv_codeValue_val tRV hNZ
    intro hLe
    have hBound : Values.vrv (u j) ≤ Values.vrv tRV := (Values.vrv_le_iff (u j) tRV).mpr hLe
    rw [← hValue,hValueAt] at hBound
    exact (not_le_of_gt hCut) hBound

def gammaFibreValueDescent
    {A : DefSet (rawMixedSpace (M := M) r s) S}
    (f : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hConst : ∀ p q : A,p.val.2=q.val.2 → (f p).val=(f q).val) :
    Map (pureRVTagDomain A) (DefSet.univ (rawGammaPresentation (M := M)) S) :=
  descendSurjectiveMap (pureRVTagQuotient A) (pureRVTagQuotient_surjective A) f
    (fun p q he => Subtype.ext (hConst p q (congrArg Subtype.val he)))

theorem gammaFibreValueDescent_at
    {A : DefSet (rawMixedSpace (M := M) r s) S}
    (f : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hConst : ∀ p q : A,p.val.2=q.val.2 → (f p).val=(f q).val) (p : A) :
    (gammaFibreValueDescent f hConst (pureRVTagQuotient A p)).val=gammaFibreValue f p.val.2 := by
  change (descendSurjectiveMap _ _ _ _ _).val=_
  rw [descendSurjectiveMap_factor, gammaFibreValue_at f hConst p]

end DiamondIntegral.Section6
