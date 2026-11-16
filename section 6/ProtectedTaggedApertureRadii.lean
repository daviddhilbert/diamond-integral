import «section 6».UniformTaggedCovariance

/-! Canonical aperture covariance protects arbitrary proper pieces.
Compatible narrow components have exactly the same active labels on
their actual sources, and their old radii yield a common named
complementary radius without naming an RV-indexed choice of witnesses. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A P : DefSet (rawMixedSpace (M := M) n r) S}
variable {D : CentripetalData (G := G) A} {E : CentripetalData (G := G) P}

theorem ApertureRestrictionData.active_iff (h : ApertureRestrictionData D E)
    {p : Mixed M n r} (hp : p ∈ P.carrier) : p.2 ∈ E.activeTags.carrier ↔ p.2 ∈ D.activeTags.carrier := by
  constructor
  · intro hu
    by_contra hn
    apply E.focus_nonzero hp hu
    rw [h.focus p hp,D.extendedFocus_inactive hn]
  · intro hu
    by_contra hn
    apply D.focus_nonzero (h.subset hp) hu
    rw [← h.focus p hp,E.extendedFocus_inactive hn]

theorem ApertureRestrictionData.coordinate_cutoff_stable (h : ApertureRestrictionData D E)
    (p : Mixed M n r) (hp : p ∈ P.carrier) (hu : p.2 ∈ D.activeTags.carrier) (x : VF M)
    (hClose : vfValue (D.coefficient*D.extendedFocus p)<vfValue (p.1 D.coordinate-x)) :
    (Function.update p.1 D.coordinate x,p.2) ∈ P.carrier := by
  have hE : vfValue (E.coefficient*E.extendedFocus p)<vfValue (p.1 E.coordinate-x) := by
    rw [h.coefficient,h.coordinate,h.focus p hp]
    exact hClose
  have hmem := E.coordinate_cutoff_stable p hp ((h.active_iff hp).mpr hu) x hE
  simpa only [h.coordinate] using hmem

theorem protected_source_invariant_at_tagged_aperture
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (D : CentripetalData (G := G) A) (j : Fin r)
    (hTag : ∀ p ∈ A.carrier,rv M (p.1 D.coordinate)=p.2 j)
    (P : Fin k → DefSet (rawMixedSpace (M := M) n r) S)
    (E : ∀ i,CentripetalData (G := G) (P i)) (hCompat : ∀ i,ApertureRestrictionData D (E i)) :
    ∃ η : Gamma M,S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {η}} ∧ 1 ≤ η ∧
      ∀ β : Gamma M,η ≤ β → ∀ i,∀ u ∈ D.activeTags.carrier,
        AlphaInvariant (fun t => if t=D.coordinate then taggedApertureRadius D.coefficient D.coefficient_nonzero u j else β)
          (vfFibre (P i).carrier u) := by
  obtain ⟨η,hη,hη1,hInv⟩ := finite_properInvariant_uniform_named_radius h00 hc linear hκ hs hv hsmall hΓ
    (fun i => (P i).carrier) (fun i => (E i).sourceProper)
  refine ⟨η,hη,hη1,?_⟩
  intro β hηβ i u hu
  apply AlphaInvariant.combine_coordinate_radius η β _ D.coordinate (hInv i u) hηβ
  intro a ha x hClose
  apply (hCompat i).coordinate_cutoff_stable (a,u) ha hu x
  rw [← D.tagged_aperture_value j hTag (a,u) ((hCompat i).subset ha) hu]
  exact hClose

end DiamondIntegral.Section6
