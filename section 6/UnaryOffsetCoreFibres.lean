import «section 6».UnaryOffsetCoreDomains
import «section 6».BoundaryCorePreparation

/-! Whole offset-core fibres inside an RV-pullback ambient source.
The actual center and offset maps restrict to these proper cores, giving
permitted special preparations over the same original base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.UnaryFocusData
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}
variable (F : UnaryFocusData A)
variable (dMap : Map (focusActive A F.activeTags) (DefSet.univ (rawVFSpace (M := M) 1) S))
variable (d : (Fin r → RVInfinity M) → VF M)
variable (hdMap : ∀ p : focusActive A F.activeTags,(dMap p).val 0=d p.val.2)

include hdMap in
theorem offsetCoreDomain_whole_fibre
    (hRV : IsRVPullback A.carrier)
    (hCenters : ∀ u ∈ F.activeTags.carrier,((fun _ : Fin 1 => F.focus u),u) ∈ A.carrier)
    (hd : ∀ u ∈ F.activeTags.carrier,d u ≠ 0)
    (hSmall : ∀ u ∈ F.activeTags.carrier,vfValue (F.focus u) < vfValue (d u))
    (u : Fin r → RVInfinity M) (hu : u ∈ F.activeTags.carrier) (x : VF M) :
    ((fun _ : Fin 1 => x),u) ∈ (F.offsetCoreDomain dMap).carrier ↔
      x ∈ centeredGammaDisc (F.focus u) (finiteValue (d u) (hd u hu)) := by
  rw [F.mem_offsetCoreDomain dMap d hdMap,mem_centeredGammaDisc]
  constructor
  · exact fun h => h.2.2
  · intro hClose
    have hf0 : F.focus u ≠ 0 := F.sourceDoublyBounded.nonzero (hCenters u hu) 0
    have hLeading : rv M x=rv M (F.focus u) :=
      (rv_eq_iff_value_close hf0).mpr ((hSmall u hu).trans hClose)
    refine ⟨rvPullback_mem_of_sameRV hRV (hCenters u hu) ?_ rfl,hu,hClose⟩
    funext i
    fin_cases i
    exact hLeading.symm

def offsetCoreActiveInclusion : Map (focusActive (F.offsetCoreDomain dMap) F.activeTags) (focusActive A F.activeTags) :=
  Map.inclusion (fun _ hp => ⟨F.offsetCoreDomain_subset dMap hp.1,hp.2⟩)

def focusOnOffsetCore (hProper : ProperInvariant S (F.offsetCoreDomain dMap).carrier) :
    UnaryFocusData (F.offsetCoreDomain dMap) where
  activeTags := F.activeTags
  focus := F.focus
  focusMap := F.focusMap.comp (F.offsetCoreActiveInclusion dMap)
  focusMap_eq p := F.focusMap_eq (F.offsetCoreActiveInclusion dMap p)
  sourceProper := hProper
  sourceDoublyBounded := by
    obtain ⟨γ,hγ⟩ := F.sourceDoublyBounded
    exact ⟨γ,fun p hp => hγ p (F.offsetCoreDomain_subset dMap hp)⟩
  tagged p hp q hq := F.tagged p (F.offsetCoreDomain_subset dMap hp) q (F.offsetCoreDomain_subset dMap hq)
  focusRV p hp hu := F.focusRV p (F.offsetCoreDomain_subset dMap hp) hu

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

include hdMap in
theorem exists_offset_core_preparation
    (hRV : IsRVPullback A.carrier)
    (hCenters : ∀ u ∈ F.activeTags.carrier,((fun _ : Fin 1 => F.focus u),u) ∈ A.carrier)
    (hd : ∀ u ∈ F.activeTags.carrier,d u ≠ 0)
    (hSmall : ∀ u ∈ F.activeTags.carrier,vfValue (F.focus u) < vfValue (d u))
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1) :
    Nonempty (UnaryTagPreparation (G := G) (F.offsetCoreDomain dMap)) := by
  let Q := F.offsetCoreDomain dMap
  have hQ : ProperInvariant S Q.carrier := F.offsetCoreDomain_proper dMap d hdMap h00 hc hκ hs hv hd
  let H := F.focusOnOffsetCore dMap hQ
  let D : Map (focusActive Q H.activeTags) (DefSet.univ (rawVFSpace (M := M) 1) S) :=
    dMap.comp (F.offsetCoreActiveInclusion dMap)
  have hD (p : focusActive Q H.activeTags) : (D p).val 0=d p.val.2 := hdMap (F.offsetCoreActiveInclusion dMap p)
  exact H.exists_boundary_core_preparation d D hD hd
    (fun p hp => ((F.mem_offsetCoreDomain dMap d hdMap p).mp hp).2.1)
    (fun p hp hu => hSmall p.2 hu)
    (F.offsetCoreDomain_whole_fibre dMap d hdMap hRV hCenters hd hSmall)
    h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt

end DiamondIntegral.Section6.UnaryFocusData
