import «section 6».UnaryRelativeApertureFiniteness
import «section 6».ScalarGammaValues
import «section 6».NamedGammaFibreValues

/-! On an actual unary RV-pullback, any supplied original-base endpoint
map with nonnegative relative value gives admissible variable aperture
data. The label-dependent named invariance radii are constructed from the
focus graph; they are not additional existence inputs. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.UnaryFocusData
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {r : ℕ} {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}

def focusGammaMap (D : UnaryFocusData A) :
    Map (focusActive A D.activeTags) (DefSet.univ (rawGammaPresentation (M := M)) S) :=
  (scalarGammaValueMap S).comp D.focusMap

theorem focusGammaMap_value (D : UnaryFocusData A) (p : focusActive A D.activeTags) :
    (D.focusGammaMap p).val.val=vfValue (D.focus p.val.2) := by
  have hn := D.focusImage_nonzero ((D.focusMap p).val 0) (Set.mem_range_self p)
  have h := scalarGammaValueMap_nonzero S (D.focusMap p).val hn
  change (D.focusGammaMap p).val.val=vfValue ((D.focusMap p).val 0) at h
  exact h.trans (congrArg vfValue (D.focusMap_eq p))

def fallbackRadius (D : UnaryFocusData A) (u : Fin r → RVInfinity M) : Gamma M :=
  (D.sourceProper.radii u).choose 0

def activeRadius (D : UnaryFocusData A) (u : Fin r → RVInfinity M) : Gamma M :=
  if h : ∃ p : focusActive A D.activeTags,p.val.2=u then
    (D.focusGammaMap h.choose).val else D.fallbackRadius u

theorem activeRadius_value (D : UnaryFocusData A) (p : focusActive A D.activeTags) :
    (D.activeRadius p.val.2).val=vfValue (D.focus p.val.2) := by
  have h : ∃ q : focusActive A D.activeTags,q.val.2=p.val.2 := ⟨p,rfl⟩
  rw [activeRadius,dif_pos h,D.focusGammaMap_value]
  exact congrArg (fun u => vfValue (D.focus u)) h.choose_spec

theorem activeRadius_named (D : UnaryFocusData A) (u : Fin r → RVInfinity M) :
    (S ∪ Set.range (rvValues u)).Definable LRV
      {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {D.activeRadius u}} := by
  by_cases h : ∃ p : focusActive A D.activeTags,p.val.2=u
  · apply gamma_value_named_on_rv_fibre (focusActive A D.activeTags).carrier
      (gammaFormExtension D.focusGammaMap) (gammaFormExtension_graph_definable D.focusGammaMap)
      u (D.activeRadius u) ⟨h.choose.val,h.choose.property,h.choose_spec⟩
    intro p hp hpu
    rw [gammaFormExtension_at D.focusGammaMap ⟨p,hp⟩]
    apply Subtype.ext
    calc
      (D.focusGammaMap ⟨p,hp⟩).val.val=vfValue (D.focus p.2) := D.focusGammaMap_value _
      _=(D.activeRadius p.2).val := (D.activeRadius_value ⟨p,hp⟩).symm
      _=(D.activeRadius u).val := congrArg (fun u => (D.activeRadius u).val) hpu
  · rw [activeRadius,dif_neg h]
    exact (D.sourceProper.radii u).choose_spec.1 0

theorem mem_of_active_congruence (D : UnaryFocusData A) (hA : IsRVPullback A.carrier)
    (u : Fin r → RVInfinity M) (hu : u ∈ D.activeTags.carrier)
    {a b : Fin 1 → VF M} (ha : (a,u) ∈ A.carrier)
    (hab : Congruent (fun _ => D.activeRadius u) a b) : (b,u) ∈ A.carrier := by
  have hα : (D.activeRadius u).val=vfValue (a 0) :=
    (D.activeRadius_value ⟨(a,u),ha,hu⟩).trans (congrArg Values.vrv (D.focusRV (a,u) ha hu))
  have hclose : vfValue (a 0)<vfValue (b 0-a 0) := by
    rw [← hα]
    exact hab.symm 0
  have hr := (rv_eq_iff_value_close (D.sourceDoublyBounded.nonzero ha 0)).mpr hclose
  apply rvPullback_mem_of_sameRV (q := (b,u)) hA ha _ rfl
  funext i
  fin_cases i
  exact hr.symm

theorem activeRadius_invariant (D : UnaryFocusData A) (hA : IsRVPullback A.carrier)
    (u : Fin r → RVInfinity M) : AlphaInvariant (fun _ => D.activeRadius u) (vfFibre A.carrier u) := by
  by_cases h : ∃ p : focusActive A D.activeTags,p.val.2=u
  · have hu : u ∈ D.activeTags.carrier := h.choose_spec ▸ h.choose.property.2
    intro a b hab
    exact ⟨fun ha => D.mem_of_active_congruence hA u hu ha hab,
      fun hb => D.mem_of_active_congruence hA u hu hb hab.symm⟩
  · rw [activeRadius,dif_neg h]
    have hInv := (D.sourceProper.radii u).choose_spec.2
    convert hInv using 1
    funext i
    fin_cases i
    rfl

def withRelativeEndpoint (D : UnaryFocusData A) (hA : IsRVPullback A.carrier)
    (b : (Fin r → RVInfinity M) → VF M)
    (bMap : Map (focusActive A D.activeTags) (DefSet.univ (rawVFSpace 1) S))
    (hbMap : ∀ p : focusActive A D.activeTags,(bMap p).val 0=b p.val.2)
    (hbNZ : ∀ p : focusActive A D.activeTags,b p.val.2≠0)
    (hbVal : ∀ p : focusActive A D.activeTags,vfValue (D.focus p.val.2) ≤ vfValue (b p.val.2)) :
    UnaryRelativeApertureData A where
  focusData := D
  endpoint := b
  endpointMap := bMap
  endpointMap_eq := hbMap
  endpoint_nonzero := hbNZ
  endpoint_nonnegative := hbVal
  radius := D.activeRadius
  radius_definable := D.activeRadius_named
  invariant := D.activeRadius_invariant hA
  radius_le_endpoint p := (D.activeRadius_value p).trans_le (hbVal p)

end DiamondIntegral.Section6.UnaryFocusData
