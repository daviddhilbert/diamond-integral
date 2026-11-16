import «section 6».ParameterCodeImages
import «section 6».RVSetParameterTemplates
import «section 2».RVBoundCoordinates

/-! The complete leading-term image of each current mixed-domain
family is an original-base RV template. Its fibre is exactly the
actual image, and each properly bounded fibre gives a bounded RV row. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r : ℕ}

def mixedLeadingRV (x : Mixed M n r) : Fin (n+r) → RVInfinity M := Fin.append (tupleRV M x.1) x.2

def mixedLeadingRVParameterCodes (z : Fin p ⊕ (Fin n ⊕ Fin r) → M) : Fin (n+r) → M :=
  Fin.append (fun i => iRv (z (.inr (.inl i)))) (fun i => z (.inr (.inr i)))

theorem mixedLeadingRVParameterCodes_definable :
    S.DefinableMap LRV (mixedLeadingRVParameterCodes (M := M) (p := p) (n := n) (r := r)) := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [mixedLeadingRVParameterCodes,Fin.append_left] using
      (rv_scalarCode_definable (show S.DefinableFun LRV
        (fun z : Fin p ⊕ (Fin n ⊕ Fin r) → M => z (.inr (.inl j))) from Set.DefinableFun.proj LRV))
  · simpa only [mixedLeadingRVParameterCodes,Fin.append_right] using
      (show S.DefinableFun LRV (fun z : Fin p ⊕ (Fin n ⊕ Fin r) → M => z (.inr (.inr j))) from
        Set.DefinableFun.proj LRV)

theorem mixedLeadingRVParameterCodes_at (a : Fin p → M) (x : Mixed M n r) :
    mixedLeadingRVParameterCodes (Sum.elim a (mixedValues x))=rvValues (mixedLeadingRV x) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [mixedLeadingRVParameterCodes,mixedLeadingRV,rvValues,Fin.append_left]
    rfl
  · simp only [mixedLeadingRVParameterCodes,mixedLeadingRV,rvValues,Fin.append_right]
    rfl

def leadingRVImageTemplate (A : MixedSetParameterTemplate (M := M) S p n r) :
    RVSetParameterTemplate (M := M) S p (n+r) :=
  ⟨parameterCodeImage A.typedGraph mixedLeadingRVParameterCodes,
    parameterCodeImage_definable A.typedGraph A.typedGraph_definable _ mixedLeadingRVParameterCodes_definable⟩

theorem leadingRVImageTemplate_fibre (A : MixedSetParameterTemplate (M := M) S p n r) (a : Fin p → M) :
    ((leadingRVImageTemplate A).fibre a).carrier=mixedLeadingRV '' (A.fibre a).carrier := by
  ext u
  change Sum.elim a (rvValues u) ∈ parameterCodeImage A.typedGraph mixedLeadingRVParameterCodes ↔ _
  change rvValues u ∈ {z | Sum.elim a z ∈ parameterCodeImage A.typedGraph mixedLeadingRVParameterCodes} ↔ _
  rw [parameterCodeImage_at]
  constructor
  · rintro ⟨z,hz,hCode⟩
    obtain ⟨hzDom,hzA⟩ := (Set.ext_iff.mp (A.fibre_code a).symm z).mp hz
    let x := (rawMixedSpace (M := M) n r).decode ⟨z,hzDom⟩
    have hX : mixedValues x=z := mixedValues_decode _
    change mixedLeadingRVParameterCodes (Sum.elim a z)=rvValues u at hCode
    rw [← hX,mixedLeadingRVParameterCodes_at] at hCode
    exact ⟨x,hzA,rvValues_injective hCode⟩
  · rintro ⟨x,hx,rfl⟩
    refine ⟨mixedValues x,(Set.ext_iff.mp (A.fibre_code a) _).mp ?_,mixedLeadingRVParameterCodes_at a x⟩
    exact ⟨mixedValues_mem_domain x,by simpa only [decode_mixedValues] using hx⟩

theorem mixedLeadingRV_image_doublyBounded (A : Set (Mixed M n r))
    (hAD : VFDoublyBounded A) (hRV : RVSupportDoublyBounded A) :
    RVValueDoublyBounded (mixedLeadingRV '' A) := by
  obtain ⟨γ,hγ⟩ := regularized_rvBounded hAD hRV
  refine ⟨γ,?_⟩
  rintro u ⟨x,hx,rfl⟩ i
  exact hγ (regularize x) ⟨x,hx,rfl⟩ i

end DiamondIntegral.Section6
