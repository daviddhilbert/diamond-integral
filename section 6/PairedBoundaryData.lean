import «section 6».FiniteBoundaryCoreCodes
import «section 6».MixedMatchingParameters

/-! Whole paired-disc data retain the actual centers, old labels, and
both offsets in a product presentation over the original parameter base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r s n : ℕ}

def pairedBoundaryDataSpace (M : Type) [LRV.Structure M] (n : ℕ) : Space LRV M :=
  (((rawMixedSpace (M := M) 2 n).prod (rawVFSpace 1)).prod (rawVFSpace 1))

def pairedBoundaryDataCodes (p : (pairedBoundaryDataSpace M n).Carrier) : Fin n ⊕ Fin 4 → M :=
  Sum.elim (rvValues p.1.1.2)
    ![(p.1.1.1 0).val,(p.1.1.1 1).val,(p.1.2 0).val,(p.2 0).val]

def pairedBoundaryCodeIndex (n : ℕ) : Fin n ⊕ Fin 4 → ((Fin 2 ⊕ Fin n) ⊕ Fin 1) ⊕ Fin 1 :=
  Sum.elim (fun i => .inl (.inl (.inr i)))
    ![.inl (.inl (.inl 0)),.inl (.inl (.inl 1)),.inl (.inr 0),.inr 0]

theorem pairedBoundaryDataCodes_decode (z : (pairedBoundaryDataSpace M n).domain) :
    pairedBoundaryDataCodes ((pairedBoundaryDataSpace M n).decode z)=z.val ∘ pairedBoundaryCodeIndex n := by
  have hCenter := mixedValues_decode
    (⟨(z.val ∘ Sum.inl) ∘ Sum.inl,z.property.1.1⟩ : (rawMixedSpace (M := M) 2 n).domain)
  have hSource := vfValues_decode
    (⟨(z.val ∘ Sum.inl) ∘ Sum.inr,z.property.1.2⟩ : (rawVFSpace (M := M) 1).domain)
  have hTarget := vfValues_decode
    (⟨z.val ∘ Sum.inr,z.property.2⟩ : (rawVFSpace (M := M) 1).domain)
  funext i
  cases i with
  | inl i =>
      simpa only [pairedBoundaryDataCodes,pairedBoundaryDataSpace,pairedBoundaryCodeIndex,
        Space.prod,mixedValues,rvValues,Sum.elim_inr,Sum.elim_inl,Function.comp_apply] using
        congrFun hCenter (.inr i)
  | inr i =>
      fin_cases i
      · exact congrFun hCenter (.inl 0)
      · exact congrFun hCenter (.inl 1)
      · exact congrFun hSource 0
      · exact congrFun hTarget 0

def goodPairedBoundaryData (G : Set (Fin n ⊕ Fin 2 → M)) (hG : S.Definable LRV G) :
    DefSet (pairedBoundaryDataSpace M n) S := by
  refine ⟨{p | pairedBoundaryDataCodes p ∈ parameterizedPairedDiscCodes G},?_⟩
  change S.Definable LRV _
  have hEq : (pairedBoundaryDataSpace M n).preimage
      {p | pairedBoundaryDataCodes p ∈ parameterizedPairedDiscCodes G}=
      (pairedBoundaryDataSpace M n).domain ∩
        {z | z ∘ pairedBoundaryCodeIndex n ∈ parameterizedPairedDiscCodes G} := by
    ext z
    constructor
    · rintro ⟨hz,hGood⟩
      refine ⟨hz,?_⟩
      change z ∘ pairedBoundaryCodeIndex n ∈ parameterizedPairedDiscCodes G
      change pairedBoundaryDataCodes ((pairedBoundaryDataSpace M n).decode ⟨z,hz⟩) ∈
        parameterizedPairedDiscCodes G at hGood
      rwa [pairedBoundaryDataCodes_decode] at hGood
    · rintro ⟨hz,hGood⟩
      refine ⟨hz,?_⟩
      change pairedBoundaryDataCodes ((pairedBoundaryDataSpace M n).decode ⟨z,hz⟩) ∈
        parameterizedPairedDiscCodes G
      rwa [pairedBoundaryDataCodes_decode]
  rw [hEq]
  exact ((pairedBoundaryDataSpace M n).definable_domain S).inter
    ((parameterizedPairedDiscCodes_definable G hG).preimage_comp (pairedBoundaryCodeIndex n))

variable {A : DefSet (rawMixedSpace (M := M) 1 r) S} {B : DefSet (rawMixedSpace (M := M) 1 s) S}

def uniformPairedBoundaryDataMap (hc : CanonicalStructure.IsCanonical (M := M)) (f : Map A B)
    (E : DefSet (rawMixedSpace (M := M) 1 r) S) (hEA : E.carrier ⊆ A.carrier)
    (hRV : IsRVPullback A.carrier) (hD : VFDoublyBounded A.carrier) :
    Map (E.prod (positiveBoundaryCoefficients hc)) (DefSet.univ (pairedBoundaryDataSpace M (r+s)) S) :=
  (((unaryMatchingParameterMap f).comp (uniformBoundaryCenterMap hc E hEA)).pair
    (uniformTargetBoundaryOffsetMap hc (Map.id A) E hEA hRV hD)).pair
      (uniformTargetBoundaryOffsetMap hc f E hEA hRV hD) |>.toUniv

theorem uniformPairedBoundaryDataMap_codes (hc : CanonicalStructure.IsCanonical (M := M)) (f : Map A B)
    (E : DefSet (rawMixedSpace (M := M) 1 r) S) (hEA : E.carrier ⊆ A.carrier)
    (hRV : IsRVPullback A.carrier) (hD : VFDoublyBounded A.carrier)
    (z : E.prod (positiveBoundaryCoefficients hc)) :
    pairedBoundaryDataCodes (uniformPairedBoundaryDataMap hc f E hEA hRV hD z).val=
      uniformBoundaryCoreCodes hc f E hEA hRV hD z := by
  funext i
  cases i with
  | inl i => rfl
  | inr i =>
      fin_cases i
      · rfl
      · rfl
      · change ((z.val.1.1 0+z.val.2 0*z.val.1.1 0)-z.val.1.1 0).val=
          (z.val.2 0*z.val.1.1 0).val
        rw [add_sub_cancel_left]
      · rfl

end DiamondIntegral.Section6
