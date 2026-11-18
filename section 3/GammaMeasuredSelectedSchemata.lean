import «section 3».GammaDensityCodeRows
import «section 3».GammaMeasuredTypedRowValidity
import «section 5».NativeGammaPointBridge
import IntegrationSection6.GammaSelectedLabelFamilies

/-! Selected structural volume coordinates and arbitrary actual Gamma
forms give complete measured schemata. No RV-valued density is selected. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {S : Set M} {p a k : ℕ}

def gammaDensityRowReindex (p a : ℕ) : Fin (p+(a+1)) → Fin ((p+a)+1) :=
  Fin.addCases (fun i => Fin.castAdd 1 (Fin.castAdd a i))
    (Fin.addCases (fun i => Fin.castAdd 1 (Fin.natAdd p i)) (Fin.natAdd (p+a)))

theorem gammaDensityRowReindex_append (z : Fin p → M) (r : Fin a → M) (c : Fin 1 → M) :
    Fin.append (Fin.append z r) c ∘ gammaDensityRowReindex p a = Fin.append z (Fin.append r c) := by
  funext i
  refine Fin.addCases (fun j => ?_) (Fin.addCases (fun j => ?_) (fun j => ?_)) i <;>
    simp only [gammaDensityRowReindex,Function.comp_apply,Fin.addCases_left,Fin.addCases_right,Fin.append_left,Fin.append_right]

def gammaMeasuredSelectedDensity {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) p a)}
    (ω : GammaGroundVolumeForm hc B A) : Set (Fin ((p+a)+1) → M) :=
  {w | w ∘ gammaDensityRowReindex p a ∈ gammaDensityCodeRows ω}

theorem gammaMeasuredSelectedDensity_proper
    {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) p a)}
    (ω : GammaGroundVolumeForm hc B A) (w) (hw : w ∈ gammaMeasuredSelectedDensity ω) :
    ∀ i, sortEval (Fin.append (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin a => .rv)) (fun _ : Fin 1 => .rv) i) (w i) := by
  have h := gammaDensityCodeRows_proper ω _ hw
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j
    refine Fin.addCases ?_ ?_ j
    · intro j
      simpa only [Function.comp_apply,gammaDensityRowReindex,Fin.addCases_left,Fin.append_left] using h (Fin.castAdd (a+1) j)
    · intro j
      simpa only [Function.comp_apply,gammaDensityRowReindex,Fin.addCases_left,Fin.addCases_right,Fin.append_left,Fin.append_right] using h (Fin.natAdd p (Fin.castAdd 1 j))
  · intro j
    simpa only [Function.comp_apply,gammaDensityRowReindex,Fin.addCases_right,Fin.append_right] using h (Fin.natAdd p (Fin.natAdd a j))

theorem gammaMeasuredSelectedDensity_definable
    {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) p a)}
    (ω : GammaGroundVolumeForm hc B A) :
    DefinableOverBase B (Fin.append (Fin.append (fun _ : Fin p => .vf) (fun _ : Fin a => .rv)) (fun _ : Fin 1 => .rv))
      (gammaMeasuredSelectedDensity ω) := by
  apply (gammaGroundRawDefinable_iff_sortedBase (hc := hc) (ground := B) (gammaMeasuredSelectedDensity_proper ω)).mp
  exact ((gammaGroundRawDefinable_iff_sortedBase (hc := hc) (ground := B) (gammaDensityCodeRows_proper ω)).mpr
    (gammaDensityCodeRows_definable ω)).preimage_comp (gammaDensityRowReindex p a)

theorem gammaMeasuredSelectedDensity_code
    {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) p a)}
    (ω : GammaGroundVolumeForm hc B A) (w) (hw : w ∈ gammaMeasuredSelectedDensity ω) :
    w ∘ Fin.natAdd (p+a) ∈ (volumeGammaSpace hc).domain := by
  obtain ⟨_,hg,_⟩ := hw
  have he : (w ∘ gammaDensityRowReindex p a ∘ gammaDensityCodeIndices p a) ∘
      (Sum.inr : Fin 1 → (Fin p ⊕ Fin a) ⊕ Fin 1) = w ∘ Fin.natAdd (p+a) := by
    funext i
    simp only [Function.comp_apply,gammaDensityCodeIndices,gammaDensityRowReindex,Fin.addCases_right]
  exact he ▸ hg

def gammaMeasuredSelectedSchema (U : DefSet (M := M) S p a)
    (hU : GammaSetDefinable B (carrier U)) (ρ : Fin k → Fin a)
    (ω : GammaGroundVolumeForm hc B (Section5.nativeGammaPointDomain (carrier U) hU)) :
    GammaMeasuredRVSchema hc B p a k (fun _ => .vf) where
  object := gammaSelectedLabelSchema U hU ρ
  density := gammaMeasuredSelectedDensity ω
  density_definable := gammaMeasuredSelectedDensity_definable ω
  density_code := gammaMeasuredSelectedDensity_code ω

theorem gammaMeasuredSelectedSchema_density (U : DefSet (M := M) S p a)
    (hU : GammaSetDefinable B (carrier U)) (ρ : Fin k → Fin a)
    (ω : GammaGroundVolumeForm hc B (Section5.nativeGammaPointDomain (carrier U) hU))
    (x : Fin p → VF (M := M)) (r : Fin a → RV (M := M)) (c : (volumeGammaSpace hc).domain) :
    (gammaMeasuredSelectedSchema U hU ρ ω).rowDensity (vfValues x) r c ↔
      ∃ q : Section5.nativeGammaPointDomain (hc := hc) (carrier U) hU,
        q.val = (x,r) ∧ (ω q).val = (volumeGammaSpace hc).decode c := by
  change (Fin.append (Fin.append (vfValues x) (rvValues r)) c.val ∘ gammaDensityRowReindex p a ∈ gammaDensityCodeRows ω) ↔ _
  rw [gammaDensityRowReindex_append]
  exact gammaDensityCodeRows_mem ω (x,r) c

theorem gammaMeasuredSelectedSchema_valid (U : DefSet (M := M) S p a)
    (hU : GammaSetDefinable B (carrier U)) (ρ : Fin k → Fin a)
    (ω : GammaGroundVolumeForm hc B (Section5.nativeGammaPointDomain (carrier U) hU))
    (x : Fin p → VF (M := M))
    (hObject : (gammaSelectedLabelSchema U hU ρ).valid (vfValues x)) :
    (gammaMeasuredSelectedSchema U hU ρ ω).valid (vfValues x) := by
  let F := gammaMeasuredSelectedSchema U hU ρ ω
  have hD := gammaSelectedLabelSchema_domain U hU ρ x
  have hRows := gammaMeasuredSelectedSchema_density U hU ρ ω x
  apply F.valid_of_typed _ hObject
  · intro r hr
    let q : Section5.nativeGammaPointDomain (hc := hc) (carrier U) hU :=
      ⟨(x,r),(Set.ext_iff.mp hD r).mp hr⟩
    obtain ⟨c,hcValue⟩ := (volumeGammaSpace hc).onto (ω q).val
    exact ⟨c,(hRows r c).mpr ⟨q,rfl,hcValue.symm⟩⟩
  · intro r c hcValue
    obtain ⟨q,hq,_⟩ := (hRows r c).mp hcValue
    have hmem : (x,r) ∈ carrier U := hq ▸ q.property
    exact (Set.ext_iff.mp hD r).mpr hmem
  · intro r c hcValue d
    obtain ⟨q,hq,hω⟩ := (hRows r c).mp hcValue
    constructor
    · intro hd
      obtain ⟨q',hq',hω'⟩ := (hRows r d).mp hd
      have hqq : q' = q := Subtype.ext (hq'.trans hq.symm)
      exact hω.symm.trans ((congrArg (fun q => (ω q).val) hqq).symm.trans hω')
    · intro hd
      exact (hRows r d).mpr ⟨q,hq,hω.trans hd⟩

end DiamondIntegral.Section3
