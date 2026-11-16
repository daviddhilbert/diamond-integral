import «section 6».CentripetalUniformErasedCovariance

/-! Canonical aperture radii from a retained coordinate tag and the
actual named coefficient. Every proper RV representative is retained
in the radius name; focus values and code values agree exactly. -/

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

def taggedApertureRadius (c : VF M) (hc0 : c ≠ 0) (u : Fin r → RVInfinity M) (k : Fin r) : Gamma M :=
  if (u k).val ≠ iRVZero then finiteValue c hc0 * GammaParameters.codeValue (u k).val else 1

theorem taggedApertureRadius_named
    (hc : CanonicalStructure.IsCanonical (M := M)) (c : VF M) (hc0 : c ≠ 0)
    (hcdef : S.Definable₁ LRV {c.val}) (u : Fin r → RVInfinity M) (k : Fin r) :
    (S ∪ Set.range (rvValues u)).Definable LRV {z : Fin 1 → M |
      z 0 ∈ Values.gammaPullback {taggedApertureRadius c hc0 u k}} := by
  unfold taggedApertureRadius
  split_ifs with ht
  · exact gamma_mul_named hc _ _ ((finiteValue_named c hc0 hcdef).mono Set.subset_union_left)
      (gamma_codeValue_named (S ∪ Set.range (rvValues u)) (u k).val ⟨(u k).property,ht⟩
        (Or.inr (Set.mem_range_self k)))
  · exact gamma_one_named hc

theorem CentripetalData.tagged_aperture_value
    {A : DefSet (rawMixedSpace (M := M) n r) S} (D : CentripetalData (G := G) A)
    (k : Fin r) (hTag : ∀ p ∈ A.carrier,rv M (p.1 D.coordinate)=p.2 k)
    (p : Mixed M n r) (hp : p ∈ A.carrier) (hu : p.2 ∈ D.activeTags.carrier) :
    (taggedApertureRadius D.coefficient D.coefficient_nonzero p.2 k).val=
      vfValue (D.coefficient*D.extendedFocus p) := by
  have ht : (p.2 k).val ≠ iRVZero := by
    intro he
    have hZero : rv M (p.1 D.coordinate)=rvZero M :=
      (hTag p hp).trans (Subtype.ext he)
    exact D.sourceDoublyBounded.nonzero hp D.coordinate ((rv_eq_zero_iff _).mp hZero)
  have hFocus : rv M (D.extendedFocus p)=p.2 k := by
    rw [D.extendedFocus_active hp hu]
    exact (D.focusRV p hp hu).trans (hTag p hp)
  rw [taggedApertureRadius,if_pos ht]
  change vfValue D.coefficient*(GammaParameters.codeValue (p.2 k).val).val=_
  rw [nonzero_rv_codeValue_val (p.2 k) (fun h => ht (congrArg Subtype.val h))]
  have hMul : vfValue (D.coefficient*D.extendedFocus p)=vfValue D.coefficient*vfValue (D.extendedFocus p) :=
    Values.vfValueHom.map_mul _ _
  rw [hMul,show vfValue (D.extendedFocus p)=Values.vrv (p.2 k) from congrArg Values.vrv hFocus]

theorem CentripetalData.source_invariant_at_tagged_aperture
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    {A : DefSet (rawMixedSpace (M := M) n r) S} (D : CentripetalData (G := G) A)
    (k : Fin r) (hTag : ∀ p ∈ A.carrier,rv M (p.1 D.coordinate)=p.2 k) :
    ∃ η : Gamma M,S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {η}} ∧ 1 ≤ η ∧
      ∀ β : Gamma M,η ≤ β → ∀ u ∈ D.activeTags.carrier,
        AlphaInvariant (fun i => if i=D.coordinate then taggedApertureRadius D.coefficient D.coefficient_nonzero u k else β)
          (vfFibre A.carrier u) := by
  obtain ⟨η,hη,hη1,hInv⟩ := properInvariant_uniform_named_radius h00 hc linear hκ hs hv hsmall hΓ D.sourceProper
  refine ⟨η,hη,hη1,?_⟩
  intro β hηβ u hu
  apply AlphaInvariant.combine_coordinate_radius η β _ D.coordinate (hInv u) hηβ
  intro a ha x hClose
  have hCut : vfValue (D.coefficient*D.extendedFocus (a,u))<vfValue (a D.coordinate-x) := by
    rw [← D.tagged_aperture_value k hTag (a,u) ha hu]
    exact hClose
  exact D.coordinate_cutoff_stable (a,u) ha hu x hCut

end DiamondIntegral.Section6
