import «section 3».GammaCompleteCodeForms
import «section 3».GammaMeasuredRowPresentations
import IntegrationSection6.GammaSchemaIndexedPresentations

/-! Indexed finite-volume objects carry the original Gamma density.
Only the structural volume acquires the index contribution. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a d k : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}
variable (F : GammaMeasuredRVSchema hc B p a (k+1) (fun _ => .rv))
variable (BP : GammaFiniteGraphPresentation B p d T R)
variable (hF : ∀ t ∈ T, F.valid (rvValues t)) (P : F.object.IndexedPresentation BP)

theorem GammaMeasuredRVSchema.indexed_mem
    (u : Section5.nativeRVGroundDomain (hc := hc) (gammaUniversalObject P.toGamma)) :
    u.val ∈ indexedDomain T (fun t => F.object.rowDomain (rvValues t)) :=
  P.domain_eq.le (Section5.nativeRVGroundDomainEquiv (gammaUniversalObject P.toGamma) u).property

theorem GammaMeasuredRVSchema.indexed_domain_eq :
    (Section5.nativeRVGroundDomain (hc := hc) (gammaUniversalObject P.toGamma)).carrier =
      indexedDomain T (fun t => F.object.rowDomain (rvValues t)) := by
  rw [Section5.nativeRVGroundDomain_carrier]
  exact P.domain_eq

def GammaMeasuredRVSchema.indexedGammaValue
    (u : Section5.nativeRVGroundDomain (hc := hc) (gammaUniversalObject P.toGamma)) :
    (volumeGammaSpace hc).Carrier :=
  F.rowGammaValue (rvValues (indexedLeft u.val)) (hF _ (F.indexed_mem BP P u).1)
    ⟨indexedRight u.val,(F.indexed_mem BP P u).2⟩

def GammaMeasuredRVSchema.indexedForm :
    GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain (gammaUniversalObject P.toGamma)) := by
  let A := Section5.nativeRVGroundDomain (hc := hc) (gammaUniversalObject P.toGamma)
  have hSort : Fin.append (Fin.append (fun _ : Fin p => SortTag.rv) (fun _ : Fin a => .rv))
      (fun _ : Fin 1 => .rv) = (fun _ => .rv) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.append_left]
      refine Fin.addCases (fun _ => ?_) (fun _ => ?_) j <;> simp only [Fin.append_left,Fin.append_right]
    · simp only [Fin.append_right]
  have hFD : DefinableOverBase B (fun _ => .rv) F.density := hSort ▸ F.density_definable
  have hRawF : GammaGroundRawDefinable hc B F.density :=
    (gammaGroundRawDefinable_iff_sortedBase (hc := hc) (ground := B) hFD.proper).mpr hFD
  have hRawA : GammaGroundRawDefinable hc B (rvValues '' A.carrier) :=
    (gammaGroundRawDefinable_iff_sortedBase (hc := hc) (ground := B)
      (gammaGroundDefinable_iff_rvBase.mp A.definable).proper).mpr
      (gammaGroundDefinable_iff_rvBase.mp A.definable)
  let D := F.density ∩ {w | w ∘ Fin.castAdd 1 ∈ rvValues '' A.carrier}
  have hRawD : GammaGroundRawDefinable hc B D :=
    hRawF.inter (hRawA.preimage_comp (Fin.castAdd 1))
  have hD : DefinableOverBase B (fun _ => .rv) D :=
    (gammaGroundRawDefinable_iff_sortedBase (hc := hc) (ground := B)
      (fun w hw => hFD.proper w hw.1)).mp hRawD
  apply gammaCompleteCodeForm A (F.indexedGammaValue BP hF P) D hD
    (fun w hw => F.density_code w hw.1)
  intro x c
  have hSplit : Fin.append (rvValues (indexedLeft x)) (rvValues (indexedRight x)) = rvValues x := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp only [rvValues,indexedLeft,indexedRight,Function.comp_apply,Fin.append_left,Fin.append_right]
  constructor
  · rintro ⟨hd,ha⟩
    have ha' : rvValues x ∈ rvValues '' A.carrier := by
      change (Fin.append (rvValues x) c.val ∘ Fin.castAdd 1) ∈ rvValues '' A.carrier at ha
      simpa only [Function.comp_def,Fin.append_left] using ha
    obtain ⟨r,hr,he⟩ := ha'
    have hrx : r = x := rvValues_injective he
    subst r
    let u : A := ⟨x,hr⟩
    refine ⟨u,rfl,?_⟩
    symm
    apply (F.rowGammaValue_graph _ (hF _ (F.indexed_mem BP P u).1)
      ⟨indexedRight x,(F.indexed_mem BP P u).2⟩ c).mp
    change Fin.append (Fin.append _ _) c.val ∈ F.density
    rw [hSplit]
    exact hd
  · rintro ⟨u,hu,hv⟩
    subst x
    refine ⟨?_,?_⟩
    · have hd := (F.rowGammaValue_graph _ (hF _ (F.indexed_mem BP P u).1)
        ⟨indexedRight u.val,(F.indexed_mem BP P u).2⟩ c).mpr hv.symm
      change Fin.append (Fin.append _ _) c.val ∈ F.density at hd
      rwa [hSplit] at hd
    · have he : Fin.append (rvValues u.val) c.val ∘ Fin.castAdd 1 = rvValues u.val := by
        funext j
        simp only [Function.comp_apply,Fin.append_left]
      change (Fin.append (rvValues u.val) c.val ∘ Fin.castAdd 1) ∈ rvValues '' A.carrier
      rw [he]
      exact ⟨u.val,u.property,rfl⟩

@[simp] theorem GammaMeasuredRVSchema.indexedForm_value
    (u : Section5.nativeRVGroundDomain (hc := hc) (gammaUniversalObject P.toGamma)) :
    (F.indexedForm BP hF P u).val = F.indexedGammaValue BP hF P u := rfl

def GammaMeasuredRVSchema.indexedObject : GammaGroundMeasuredRVObject hc B ((d+k)+1) :=
  gammaNativeMeasuredNormalization (gammaUniversalObject P.toGamma)
    (F.indexedForm BP hF P)

end DiamondIntegral.Section3
