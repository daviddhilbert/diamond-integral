import «section 5».Completed18GroundRVObjects
import IntegrationSection6.GammaNativeFiniteBounds

/-! Reverse conversion of full-weight original-Gamma RV objects, retaining
actual domain points and the entire finite label graph. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.DefinableGeometry.Space.ofEmbedding
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
open DiamondIntegral.Section3 DiamondIntegral.Section4
open FiniteTupleBlocks RVMeasuredCharts Section3RVCodeBridge
namespace DiamondIntegral.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {k : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

def nativeRVRawVolume (U : GammaObjectAt B Set.univ k)
    (x : Fin (SpecialTransformations.Section5.rvObjectArity U.object.obj) → M) : Fin k → M :=
  if hx : x ∈ gammaRawObjectDomain U.toGamma.toGammaRVObject then
    (gammaRawObjectVolume_unique U.toGamma.toGammaRVObject x hx).exists.choose
  else fun _ => iRVZero

theorem nativeRVRawVolume_spec (U : GammaObjectAt B Set.univ k)
    {x : Fin (SpecialTransformations.Section5.rvObjectArity U.object.obj) → M}
    (hx : x ∈ gammaRawObjectDomain U.toGamma.toGammaRVObject) :
    Fin.append x (nativeRVRawVolume U x) ∈ gammaRawObjectVolume U.toGamma.toGammaRVObject := by
  simpa only [nativeRVRawVolume,dif_pos hx] using
    (gammaRawObjectVolume_unique U.toGamma.toGammaRVObject x hx).exists.choose_spec

theorem nativeRVRawVolume_eq (U : GammaObjectAt B Set.univ k)
    {x : Fin (SpecialTransformations.Section5.rvObjectArity U.object.obj) → M}
    {y : Fin k → M} (h : Fin.append x y ∈ gammaRawObjectVolume U.toGamma.toGammaRVObject) :
    nativeRVRawVolume U x = y := by
  obtain ⟨u,hu,hv⟩ := (gammaRawObjectVolume_append_iff U.toGamma.toGammaRVObject x y).mp h
  exact (gammaRawObjectVolume_unique U.toGamma.toGammaRVObject x ⟨u,hu⟩).unique
    (nativeRVRawVolume_spec U ⟨u,hu⟩) h

theorem nativeRVRawVolume_proper (U : GammaObjectAt B Set.univ k)
    (x : Fin (SpecialTransformations.Section5.rvObjectArity U.object.obj) → M)
    (hx : x ∈ gammaRawObjectDomain U.toGamma.toGammaRVObject) (i : Fin k) :
    iRV (nativeRVRawVolume U x i) := by
  have hp := (gammaRawObjectVolume_definable U.toGamma.toGammaRVObject).proper _
    (nativeRVRawVolume_spec U hx) (Fin.natAdd _ i)
  change iRV (Fin.append x (nativeRVRawVolume U x) (Fin.natAdd _ i)) at hp
  simpa only [Fin.append_right] using hp

theorem join_rv_proper {a k : ℕ} (x : Fin a → M) (y : Fin k → M)
    (hx : ∀ i,iRV (x i)) (hy : ∀ i,iRV (y i)) :
    ∀ i,iRV (join k a x y i) := by
  induction a with
  | zero => exact hy
  | succ a ih =>
    intro i
    refine Fin.cases (hx 0) (fun j => ?_) i
    exact ih (Fin.tail x) (fun j => hx j.succ) j

theorem nativeRVRawVolume_graph (U : GammaObjectAt B Set.univ k) :
    DefinableOverBase B (fun _ => .rv)
      (graphOn (gammaRawObjectDomain U.toGamma.toGammaRVObject) (nativeRVRawVolume U)) := by
  let a := SpecialTransformations.Section5.rvObjectArity U.object.obj
  let π : Fin (a+k) → Fin (k+a) := Fin.append (headIndex k a) (tailIndex k a)
  have h := (gammaRawObjectVolume_definable U.toGamma.toGammaRVObject).preimage_real
    (fun _ : Fin (k+a) => .rv) π
  suffices he : {z : Fin (k+a) → M | z ∘ π ∈ gammaRawObjectVolume U.toGamma.toGammaRVObject ∧
      z ∈ sortedUniverse (fun _ => .rv)} =
      graphOn (gammaRawObjectDomain U.toGamma.toGammaRVObject) (nativeRVRawVolume U) by
    exact he ▸ h
  ext z
  have he : z ∘ π = Fin.append (z ∘ headIndex k a) (z ∘ tailIndex k a) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp only [Function.comp_apply,π,Fin.append_left,Fin.append_right]
  change (_ ∈ _ ∧ _) ↔ (_ ∧ _)
  rw [he]
  constructor
  · rintro ⟨hz,hp⟩
    obtain ⟨u,hu,hv⟩ := (gammaRawObjectVolume_append_iff U.toGamma.toGammaRVObject _ _).mp hz
    exact ⟨⟨u,hu⟩,nativeRVRawVolume_eq U hz⟩
  · rintro ⟨hz,hv⟩
    have hs := nativeRVRawVolume_spec U hz
    rw [hv] at hs
    refine ⟨hs,?_⟩
    have hx := (gammaRawObjectDomain_definable U.toGamma.toGammaRVObject).proper _ hz
    have hy : ∀ i,iRV ((z ∘ tailIndex k a) i) := by
      intro i
      exact (congrArg iRV (congrFun hv i)).mp (nativeRVRawVolume_proper U _ hz i)
    have hp := join_rv_proper (z ∘ headIndex k a) (z ∘ tailIndex k a) hx hy
    rw [join_reconstruct] at hp
    exact hp

def nativeRVGroundDomain (U : GammaObjectAt B Set.univ k) :=
  ofRaw (hc := hc) (gammaRawObjectDomain U.toGamma.toGammaRVObject)
    (gammaRawObjectDomain_definable U.toGamma.toGammaRVObject)

def nativeRVGroundVolume (U : GammaObjectAt B Set.univ k) :
    GammaGroundMap (nativeRVGroundDomain (hc := hc) U)
      (GammaGroundDefSet.univ hc B (rawRVSpace k)) :=
  mapOfRaw _ (gammaRawObjectDomain_definable U.toGamma.toGammaRVObject)
    (nativeRVRawVolume U) (nativeRVRawVolume_graph U) (nativeRVRawVolume_proper U)

theorem nativeRVGroundVolume_finite (U : GammaObjectAt B Set.univ k) :
    (nativeRVGroundVolume (hc := hc) U).FiniteFibres := by
  intro t
  apply Set.Finite.of_injOn (f := fun a : nativeRVGroundDomain (hc := hc) U => rvValues a.val)
    (t := {x | Fin.append x (rvValues t.val) ∈ gammaRawObjectVolume U.toGamma.toGammaRVObject})
  · intro a ha
    have he : nativeRVRawVolume U (rvValues a.val) = rvValues t.val :=
      congrArg (fun v : GammaGroundDefSet.univ hc B (rawRVSpace k) => rvValues v.val) ha
    rw [← he]
    exact nativeRVRawVolume_spec U a.property
  · intro a ha b hb he
    exact Subtype.ext (rvValues_injective he)
  · exact gammaRawObjectVolume_fibre_finite U.toGamma _

theorem nativeRVGroundVolume_nonzero (U : GammaObjectAt B Set.univ k)
    (hU : GammaFullWeightAt U) (a : nativeRVGroundDomain (hc := hc) U) (i : Fin k) :
    (((nativeRVGroundVolume (hc := hc) U) a).val i).val ≠ iRVZero := by
  obtain ⟨u,hu,hv⟩ := (gammaRawObjectVolume_append_iff U.toGamma.toGammaRVObject _ _).mp
    (nativeRVRawVolume_spec U a.property)
  change nativeRVRawVolume U (rvValues a.val) i ≠ iRVZero
  rw [← hv]
  cases k with
  | zero => exact Fin.elim0 i
  | succ k =>
    intro he
    have hz : @iRVZero M N = @iRVZero M sM := CanonicalStructure.sortZero_normalize .rv
    have he' : ((SpecialTransformations.Section5.rvObjectVolume U.object.obj u).val i).val =
        @iRVZero M N := he.trans hz.symm
    have hl := (@rvWeight_le_pred_iff_zero M N k
      (SpecialTransformations.Section5.rvObjectVolume U.object.obj u).val).mpr ⟨i,he'⟩
    have hw := hU u
    change @rvWeight M N (k+1)
      (SpecialTransformations.Section5.rvObjectVolume U.object.obj u).val = k+1 at hw
    rw [hw] at hl
    exact Nat.not_succ_le_self k hl

def nativeRVGroundObject (U : GammaObjectAt B Set.univ k) (hU : GammaFullWeightAt U) :
    GammaGroundRVObject hc B k where
  arity := SpecialTransformations.Section5.rvObjectArity U.object.obj
  domain := nativeRVGroundDomain U
  volume := nativeRVGroundVolume U
  finite := nativeRVGroundVolume_finite U
  nonzero := nativeRVGroundVolume_nonzero U hU

end DiamondIntegral.Section5
