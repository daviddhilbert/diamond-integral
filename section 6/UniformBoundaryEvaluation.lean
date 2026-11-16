import «section 6».NamedUnaryOffsets
import «section 6».NamedEventualVFChoices

/-! The coefficient is a genuine varying VF input. Both the boundary
point and its image offset have complete original-base definable graphs;
no particular coefficient or target-radius representative is named. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r s : ℕ}

def positiveBoundaryCoefficients (hc : CanonicalStructure.IsCanonical (M := M)) : DefSet (rawVFSpace (M := M) 1) S := by
  refine ⟨puncturedRadiusBall (1 : Gamma M),?_⟩
  change S.Definable LRV ((rawVFSpace (M := M) 1).preimage (puncturedRadiusBall (1 : Gamma M)))
  have hEq : (rawVFSpace (M := M) 1).preimage (puncturedRadiusBall (1 : Gamma M))=
      vfValues '' puncturedRadiusBall (1 : Gamma M) := by
    ext z
    constructor
    · rintro ⟨hz,hP⟩
      exact ⟨(rawVFSpace (M := M) 1).decode ⟨z,hz⟩,hP,vfValues_decode _⟩
    · rintro ⟨p,hp,rfl⟩
      refine ⟨Set.mem_range_self p,?_⟩
      have hDecode : (rawVFSpace (M := M) 1).decode ⟨vfValues p,Set.mem_range_self p⟩=p :=
        vfValues_injective (vfValues_decode _)
      exact hDecode.symm ▸ hp
  rw [hEq]
  exact puncturedRadiusBall_definable 1 (gamma_one_named hc)

def unaryBoundaryPoint (c : VF M) (p : Mixed M 1 r) : Mixed M 1 r :=
  ((fun i => p.1 i+c*p.1 i),p.2)

def uniformBoundaryPointMap (hc : CanonicalStructure.IsCanonical (M := M))
    (E : DefSet (rawMixedSpace (M := M) 1 r) S) :
    Map (E.prod (positiveBoundaryCoefficients hc)) (DefSet.univ (rawMixedSpace (M := M) 1 r) S) := by
  let P := (rawMixedSpace (M := M) 1 r).prod (rawVFSpace 1)
  let f (p : P.Carrier) := unaryBoundaryPoint (p.2 0) p.1
  let F (z : (Fin 1 ⊕ Fin r) ⊕ Fin 1 → M) : Fin 1 ⊕ Fin r → M :=
    Sum.elim (fun i => iVFAdd (z (.inl (.inl i))) (iVFMul (z (.inr 0)) (z (.inl (.inl i)))))
      (fun j => z (.inl (.inr j)))
  have hF : S.DefinableMap LRV F := by
    rintro (i | j)
    · exact scalarAddCode_definable (Set.DefinableFun.proj LRV)
        (scalarMulCode_definable (Set.DefinableFun.proj LRV) (Set.DefinableFun.proj LRV))
    · exact Set.DefinableFun.proj LRV
  have hCode (z : P.domain) : mixedValues (f (P.decode z))=F z.val := by
    have hLeft := mixedValues_decode (⟨z.val ∘ Sum.inl,z.property.1⟩ : (rawMixedSpace (M := M) 1 r).domain)
    have hRight := vfValues_decode (⟨z.val ∘ Sum.inr,z.property.2⟩ : (rawVFSpace (M := M) 1).domain)
    funext i
    cases i with
    | inl i =>
        exact congrArg₂ iVFAdd (congrFun hLeft (.inl i))
          (congrArg₂ iVFMul (congrFun hRight 0) (congrFun hLeft (.inl i)))
    | inr j =>
        simpa only [f,unaryBoundaryPoint,F,mixedValues,Sum.elim_inr,rvValues,Function.comp_apply,P,Space.prod] using congrFun hLeft (.inr j)
  exact Map.ofCodes (E.prod (positiveBoundaryCoefficients hc)) f F hF
    (fun z => (hCode z) ▸ mixedValues_mem_domain (f (P.decode z)))
    (fun z => mixedValues_injective ((mixedValues_decode _).trans (hCode z).symm))

theorem uniformBoundaryPointMap_value (hc : CanonicalStructure.IsCanonical (M := M))
    (E : DefSet (rawMixedSpace (M := M) 1 r) S) (p : E.prod (positiveBoundaryCoefficients hc)) :
    (uniformBoundaryPointMap hc E p).val=unaryBoundaryPoint (p.val.2 0) p.val.1 := rfl

variable {A : DefSet (rawMixedSpace (M := M) 1 r) S} {B : DefSet (rawMixedSpace (M := M) 1 s) S}

theorem unaryBoundaryPoint_mem (c : VF M) (hc0 : c ≠ 0) (hcPos : (1 : GammaInfinity M) < vfValue c)
    (hRV : IsRVPullback A.carrier) (hD : VFDoublyBounded A.carrier) (p : Mixed M 1 r) (hp : p ∈ A.carrier) :
    unaryBoundaryPoint c p ∈ A.carrier := by
  apply rvPullback_mem_of_sameRV (q := unaryBoundaryPoint c p) hRV hp _ rfl
  funext i
  fin_cases i
  have hp0 : p.1 0 ≠ 0 := hD.nonzero hp 0
  apply Eq.symm
  apply (rv_eq_iff_value_close hp0).mpr
  change vfValue (p.1 0) < vfValue ((p.1 0+c*p.1 0)-p.1 0)
  simpa only [add_sub_cancel_left] using vf_value_lt_positive_named_offset (p.1 0) c hp0 hc0 hcPos

def uniformBoundaryMap (hc : CanonicalStructure.IsCanonical (M := M))
    (E : DefSet (rawMixedSpace (M := M) 1 r) S) (hEA : E.carrier ⊆ A.carrier)
    (hRV : IsRVPullback A.carrier) (hD : VFDoublyBounded A.carrier) :
    Map (E.prod (positiveBoundaryCoefficients hc)) A where
  toFun p := ⟨(uniformBoundaryPointMap hc E p).val,
    unaryBoundaryPoint_mem (p.val.2 0) p.property.2.1 p.property.2.2 hRV hD p.val.1 (hEA p.property.1)⟩
  graph_definable := (uniformBoundaryPointMap hc E).graph_definable

def uniformBoundaryCenterMap (hc : CanonicalStructure.IsCanonical (M := M))
    (E : DefSet (rawMixedSpace (M := M) 1 r) S) (hEA : E.carrier ⊆ A.carrier) :
    Map (E.prod (positiveBoundaryCoefficients hc)) A where
  toFun p := ⟨p.val.1,hEA p.property.1⟩
  graph_definable := (Map.fst (rawMixedSpace (M := M) 1 r) (rawVFSpace 1) S
    (E.prod (positiveBoundaryCoefficients hc))).graph_definable

def uniformTargetBoundaryOffsetMap (hc : CanonicalStructure.IsCanonical (M := M)) (f : Map A B)
    (E : DefSet (rawMixedSpace (M := M) 1 r) S) (hEA : E.carrier ⊆ A.carrier)
    (hRV : IsRVPullback A.carrier) (hD : VFDoublyBounded A.carrier) :
    Map (E.prod (positiveBoundaryCoefficients hc)) (DefSet.univ (rawVFSpace (M := M) 1) S) :=
  (vfTupleBinaryMap S .sub).comp ((Map.inclusion (fun _ _ => Set.mem_univ _)).comp
    (((mixedVFHeadMap B).comp (f.comp (uniformBoundaryMap hc E hEA hRV hD))).pair
      ((mixedVFHeadMap B).comp (f.comp (uniformBoundaryCenterMap hc E hEA)))))

theorem uniformTargetBoundaryOffsetMap_value (hc : CanonicalStructure.IsCanonical (M := M)) (f : Map A B)
    (E : DefSet (rawMixedSpace (M := M) 1 r) S) (hEA : E.carrier ⊆ A.carrier)
    (hRV : IsRVPullback A.carrier) (hD : VFDoublyBounded A.carrier)
    (p : E.prod (positiveBoundaryCoefficients hc)) :
    (uniformTargetBoundaryOffsetMap hc f E hEA hRV hD p).val 0=
      (f (uniformBoundaryMap hc E hEA hRV hD p)).val.1 0-(f (uniformBoundaryCenterMap hc E hEA p)).val.1 0 := rfl

end DiamondIntegral.Section6
