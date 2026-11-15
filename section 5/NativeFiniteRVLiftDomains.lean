import «section 5».NativeFiniteRVSchemaValidity
import «section 5».NativeMixedCodeBridge
import «section 3».GammaGroundLifting
import Section3.GammaRealMap

/-! The actual VF lift of a finite native RV row has a fixed full
original-language domain formula, including every old RV representative.
The new VF variables lift only the finite label tuple. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVCodeBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {p a k : ℕ} {sp : Fin p → SortTag}

def finiteRVLiftCoordinates (w : Fin (p+(k+a)) → M) : Fin ((p+a)+k) → M :=
  Fin.append (Fin.append (w ∘ Fin.castAdd (k+a))
    (fun j => w (Fin.natAdd p (Fin.natAdd k j))))
      (fun j => iRv (w (Fin.natAdd p (Fin.castAdd a j))))

theorem finiteRVLiftCoordinates_append (z : Fin p → M) (x : Fin k → M) (u : Fin a → M) :
    finiteRVLiftCoordinates (Fin.append z (Fin.append x u)) = Fin.append (Fin.append z u) (fun j => iRv (x j)) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · refine Fin.addCases (fun l => ?_) (fun l => ?_) j <;>
      simp only [finiteRVLiftCoordinates,Fin.append_left,Fin.append_right,Function.comp_apply]
  · simp only [finiteRVLiftCoordinates,Fin.append_left,Fin.append_right,Function.comp_apply]

theorem finiteRVLiftCoordinates_definable (hc : CanonicalStructure.IsCanonical (M := M)) :
    @Set.DefinableMap M LRV (CanonicalStructure.normalize (M := M)) (Fin (p+(k+a))) (Fin ((p+a)+k)) B.real
      (finiteRVLiftCoordinates (M := M) (p := p) (a := a) (k := k)) := by
  rw [canonical_normalize_eq hc]
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · refine Fin.addCases (fun l => ?_) (fun l => ?_) j
    · simp only [finiteRVLiftCoordinates,Fin.append_left,Fin.append_right,Function.comp_apply]
      exact Set.DefinableFun.proj LRV
    · simp only [finiteRVLiftCoordinates,Fin.append_left,Fin.append_right,Function.comp_apply]
      exact Set.DefinableFun.proj LRV
  · simp only [finiteRVLiftCoordinates,Fin.append_left,Fin.append_right,Function.comp_apply]
    exact (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.rvMap)).comp
      (show B.real.DefinableMap LRV
        (fun w : Fin (p+(k+a)) → M => ![w (Fin.natAdd p (Fin.castAdd a j))]) from
          fun i => by fin_cases i; exact Set.DefinableFun.proj LRV)

def finiteRVSchemaLiftDomain (hc : CanonicalStructure.IsCanonical (M := M))
    (F : GammaFiniteRVSchema B p a k sp) :
    {D : Set (Fin (p+(k+a)) → M) // DefinableOverBase B
      (Fin.append sp (Fin.append (fun _ : Fin k => .vf) (fun _ : Fin a => .rv))) D} :=
  ⟨{w | finiteRVLiftCoordinates w ∈ F.volume ∧ w ∈ sortedUniverse
      (Fin.append sp (Fin.append (fun _ : Fin k => .vf) (fun _ : Fin a => .rv)))},
    F.volume_definable.preimage_real_map _ _ (finiteRVLiftCoordinates_definable hc)⟩

theorem finiteRVSchemaLiftDomain_row (hc : CanonicalStructure.IsCanonical (M := M))
    (F : GammaFiniteRVSchema B p a k sp) (z : Fin p → M) (x : Fin k → M) (u : Fin a → M)
    (hz : ∀ i, sortEval (sp i) (z i)) (hx : ∀ i, iVF (x i)) (hu : ∀ i, iRV (u i)) :
    Fin.append z (Fin.append x u) ∈ (finiteRVSchemaLiftDomain hc F).val ↔
      Fin.append (Fin.append z u) (fun j => iRv (x j)) ∈ F.volume := by
  change (finiteRVLiftCoordinates (Fin.append z (Fin.append x u)) ∈ F.volume ∧ _) ↔ _
  rw [finiteRVLiftCoordinates_append]
  constructor
  · exact And.left
  · intro h
    refine ⟨h,?_⟩
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left] using hz j
    · refine Fin.addCases (fun l => ?_) (fun l => ?_) j
      · simpa only [Fin.append_right,Fin.append_left,sortEval,iVF] using hx l
      · simpa only [Fin.append_right,Fin.append_right,sortEval,iRV] using hu l

theorem finiteRVSchemaLiftDomain_native_row
    (F : GammaFiniteRVSchema B p a k sp) (z : Fin p → M) (hv : nativeFiniteRVSchemaValid F z)
    (q : Section2.Mixed M k a) :
    Fin.append z (nativeMixedCode q) ∈ (finiteRVSchemaLiftDomain hc F).val ↔
      q ∈ (gammaGroundObjectLift (nativeFiniteRVSchemaObject (hc := hc) F z hv)).carrier := by
  have hrow : Fin.append z (nativeMixedCode q) ∈ (finiteRVSchemaLiftDomain hc F).val ↔
      Fin.append (Fin.append z (rvValues q.2)) (rvValues (Section2.tupleRV M q.1)) ∈ F.volume :=
    finiteRVSchemaLiftDomain_row hc F z (vfValues q.1) (rvValues q.2) hv.1.1
      (fun i => (q.1 i).property) (fun i => (q.2 i).property)
  refine hrow.trans ?_
  constructor
  · intro h
    have hsrc := hv.1.2.2.1 _ _ h
    let u : (nativeFiniteRVSchemaObject (hc := hc) F z hv).domain := ⟨q.2,hsrc⟩
    refine ⟨u,rfl,?_⟩
    apply rvValues_injective
    exact (finiteRVSchemaNativeObject_label_graph F z hv.1 hv.2 u _).mp h
  · rintro ⟨u,hu,hp⟩
    have h := (finiteRVSchemaNativeObject_label_graph F z hv.1 hv.2 u _).mpr (congrArg rvValues hp)
    exact hu ▸ h

end DiamondIntegral.Section5
