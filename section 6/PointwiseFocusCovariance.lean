import «section 6».FullFocusValueRadii

/-! Permitted component covariance in a form with only finite named
metadata and pointwise conditions on complete focus graphs. The active
radius is reconstructed from the graph and coefficient, rather than
chosen separately for every RV fibre. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

structure PointwiseFocusCovariance (F : FullFocusGraphData (G := G) A) where
  coefficient : VF M
  nonzero : coefficient ≠ 0
  nonnegative : (1 : GammaInfinity M) ≤ vfValue coefficient
  coefficient_named : S.Definable₁ LRV {coefficient.val}
  radius : Gamma M
  radius_named : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {radius}}
  source : ∀ p : focusActive A F.activeTags,∀ b : Fin n → VF M,
    (∀ i,(if i=F.coordinate then vfValue (coefficient*(F.map p).val 0) else radius.val)<
      vfValue (p.val.1 i-b i)) → (b,p.val.2) ∈ A.carrier
  focus : ∀ p q : focusActive A F.activeTags,p.val.2=q.val.2 →
    Congruent (fun _ => radius) (Function.update p.val.1 F.coordinate 0) (Function.update q.val.1 F.coordinate 0) →
      vfValue (coefficient*(F.map p).val 0)<vfValue ((F.map p).val 0-(F.map q).val 0)

def PointwiseFocusCovariance.fullData
    (hc : CanonicalStructure.IsCanonical (M := M)) {F : FullFocusGraphData (G := G) A}
    (C : PointwiseFocusCovariance F) : FullFocusCovarianceData F where
  coefficient := C.coefficient
  coefficient_nonzero := C.nonzero
  coefficient_nonnegative := C.nonnegative
  coefficient_definable := C.coefficient_named
  activeRadius := F.activeRadius C.coefficient C.coefficient_named
  activeNamed u _ := F.activeRadius_named hc C.coefficient C.coefficient_named C.nonzero u
  complementaryRadius := C.radius
  complementaryNamed := C.radius_named
  invariant u hu := by
    have hMove (a : Fin n → VF M) (ha : a ∈ vfFibre A.carrier u) (b : Fin n → VF M)
        (hab : Congruent (fun i => if i=F.coordinate then F.activeRadius C.coefficient C.coefficient_named u else C.radius) a b) :
        b ∈ vfFibre A.carrier u := by
      apply C.source ⟨(a,u),ha,hu⟩ b
      intro i
      have hα := F.activeRadius_value C.coefficient C.coefficient_named C.nonzero ⟨(a,u),ha,hu⟩
      by_cases hi : i=F.coordinate
      · simpa only [if_pos hi,hα] using hab i
      · simpa only [if_neg hi] using hab i
    exact fun a b hab => ⟨fun ha => hMove a ha b hab,fun hb => hMove b hb a hab.symm⟩
  covariance u hu a ha b hb hab := by
    rw [F.activeRadius_value C.coefficient C.coefficient_named C.nonzero ⟨(a,u),ha,hu⟩]
    exact C.focus ⟨(a,u),ha,hu⟩ ⟨(b,u),hb,hu⟩ rfl hab
  aperture u hu a ha := by
    rw [F.activeRadius_value C.coefficient C.coefficient_named C.nonzero ⟨(a,u),ha,hu⟩]

def FullFocusCovarianceData.toPointwise {F : FullFocusGraphData (G := G) A}
    (C : FullFocusCovarianceData F)
    (hRadius : ∀ p : focusActive A F.activeTags,(C.activeRadius p.val.2).val=
      vfValue (C.coefficient*(F.map p).val 0)) : PointwiseFocusCovariance F where
  coefficient := C.coefficient
  nonzero := C.coefficient_nonzero
  nonnegative := C.coefficient_nonnegative
  coefficient_named := C.coefficient_definable
  radius := C.complementaryRadius
  radius_named := C.complementaryNamed
  source p b hab := by
    apply (C.invariant p.val.2 p.property.2 p.val.1 b ?_).mp p.property.1
    intro i
    by_cases hi : i=F.coordinate
    · simpa only [if_pos hi,hRadius p] using hab i
    · simpa only [if_neg hi] using hab i
  focus p q hu hab := by
    have hEq : (q.val.1,p.val.2)=q.val := Prod.ext rfl hu
    have hq : (q.val.1,p.val.2) ∈ A.carrier := hEq.symm ▸ q.property.1
    have h := C.covariance p.val.2 p.property.2 p.val.1 p.property.1 q.val.1 hq hab
    rw [hRadius p] at h
    have hQ : (⟨(q.val.1,p.val.2),hq,p.property.2⟩ : focusActive A F.activeTags)=q :=
      Subtype.ext hEq
    rw [hQ] at h
    exact h

end DiamondIntegral.Section6
