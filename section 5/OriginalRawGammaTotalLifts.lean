import «section 5».OriginalRawGammaFamilies
import «section 5».RawGammaLiftRepresentatives
import «section 5».NativeSetBijections
import «section 3».GammaGroundRVProductMorphisms

/-! Literal total RV domains of full Gamma schemata are bijective to the
encoded lifts used by relative Fubini. Every representative is retained. -/
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
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p n : ℕ}

def rawGammaTotalPacking (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p)) :=
  let U := GammaGroundDefSet.univ hc B (rawRVUnitSpace (M := M) n)
  let e := gammaGroundRVUnitPresentationBijection U
  (gammaGroundRVPackBijection X (gammaGroundRVUnitToRVMap U).image).comp
    ((GammaGroundBijection.id X).prodMap e)

theorem rawGammaTotalPacking_value
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (a : X.prod (GammaGroundDefSet.univ hc B (rawRVUnitSpace (M := M) n))) :
    ((rawGammaTotalPacking X).map a).val =
      Fin.append a.val.1 (fun j => (a.val.2 j : CanonicalRV.RVSort M)) := rfl

theorem originalGammaRawUnits_row
    (D : GammaDomainFormula B p n (fun _ => .rv))
    (x : Fin p → CanonicalRV.RVSort M) (z : Fin n → (CanonicalRV.RVSort M)ˣ)
    (hD : originalGammaSourceValid hc D (rvValues x)) :
    Fin.append (rvValues x) (rvUnitValues z) ∈ D.val ↔
      rvUnitTupleValues z ∈ originalGammaSourceRow hc D (rvValues x) := by
  have hp : Proper (rvUnitValues z) := fun j =>
    ⟨(z j).val.property,fun h => (z j).ne_zero (Subtype.ext (h.trans RVOperations.zero_val.symm))⟩
  have he : codeValue ∘ rvUnitValues z = rvUnitTupleValues z := by
    funext j
    exact codeValue_raw ⟨(z j).val,(hp j).2⟩
  exact ((gammaDomainSyntax_realize hc B D (rvValues x) (rvUnitValues z)).symm.trans
    (originalGammaSourceRow_represents hc D (rvValues x) hD (rvUnitValues z))).trans
      ((and_iff_right hp).trans (Iff.of_eq (congrArg (fun γ => γ ∈ originalGammaSourceRow hc D (rvValues x)) he)))

theorem originalRVTotalFamily_subset_gamma_packing
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (D : GammaDomainFormula B p n (fun _ => .rv))
    (hD : ∀ x : X, originalGammaSourceValid hc D (rvValues x.val)) :
    (originalRVTotalFamily X D).carrier ⊆
      (gammaGroundRVProductDomain X
        (gammaGroundRVUnitToRVMap (GammaGroundDefSet.univ hc B (rawRVUnitSpace (M := M) n))).image).carrier := by
  intro u hu
  obtain ⟨hx,hd⟩ := (originalRVTotalFamily_mem X D u).mp hu
  let x : X := ⟨u ∘ Fin.castAdd n,hx⟩
  let v := rvValues (u ∘ Fin.natAdd p)
  have he : Fin.append (rvValues x.val) v = rvValues u := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp only [x,v,rvValues,Function.comp_def,Fin.append_left,Fin.append_right]
  have hp := ((originalGammaSourceRow_represents hc D (rvValues x.val) (hD x) v).mp
    ((gammaDomainSyntax_realize hc B D (rvValues x.val) v).mpr (he.symm ▸ hd))).1
  let z : Fin n → (CanonicalRV.RVSort M)ˣ := fun j => Units.mk0 (u (Fin.natAdd p j))
    (fun hz => (hp j).2 ((congrArg Subtype.val hz).trans RVOperations.zero_val))
  let a : X.prod (GammaGroundDefSet.univ hc B (rawRVUnitSpace (M := M) n)) :=
    ⟨(x.val,z),x.property,Set.mem_univ _⟩
  have hv : ((rawGammaTotalPacking X).map a).val = u := by
    rw [rawGammaTotalPacking_value]
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp only [a,x,z,Fin.append_left,Fin.append_right,Function.comp_def,Units.val_mk0]
  exact hv ▸ ((rawGammaTotalPacking X).map a).property

theorem originalRawGammaTotal_preimage
    (h00 : M ⊨ Axioms.ACVF00)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (D : GammaDomainFormula B p n (fun _ => .rv))
    (hD : ∀ x : X, originalGammaSourceValid hc D (rvValues x.val)) :
    ((rawGammaTotalPacking (n := n) X).inverseImage (originalRVTotalFamily X D)).carrier =
      (rawGammaRepresentativeDomain h00 X (originalRawGammaFamily X D hD)).carrier := by
  apply Set.ext
  rintro ⟨x,z⟩
  by_cases hx : x ∈ X.carrier
  · let a : X.prod (GammaGroundDefSet.univ hc B (rawRVUnitSpace (M := M) n)) :=
      ⟨(x,z),hx,Set.mem_univ _⟩
    have h1 := groundBijection_inverseImage_at (rawGammaTotalPacking (n := n) X)
      (originalRVTotalFamily X D) a
    have h2 := rawGammaRepresentativeDomain_row h00 X (originalRawGammaFamily X D hD) ⟨x,hx⟩ z
    refine h1.trans (Iff.trans ?_ h2.symm)
    rw [rawGammaTotalPacking_value,originalRVTotalFamily_mem]
    have hbase : Fin.append x (fun j => (z j : CanonicalRV.RVSort M)) ∘ Fin.castAdd n = x := by
      funext j
      exact Fin.append_left _ _ j
    have hvalues : rvValues (Fin.append x (fun j => (z j : CanonicalRV.RVSort M))) =
        Fin.append (rvValues x) (rvUnitValues z) := by
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
        simp only [rvValues,rvUnitValues,Fin.append_left,Fin.append_right]
    rw [hbase,hvalues,originalGammaRawUnits_row D x z (hD ⟨x,hx⟩)]
    exact Iff.rfl
  · constructor
    · intro h
      exact (hx (((rawGammaTotalPacking (n := n) X).inverseImage_subset (originalRVTotalFamily X D) h).1)).elim
    · intro h
      have hsub := (rawGammaRepresentativeBaseBijection (n := n) h00 X).inverseImage_subset
        ((rawGammaLiftPacking (n := n) X).inverseImage
          (rawRVGammaLift h00 X (originalRawGammaFamily X D hD))) h
      exact (hx hsub.1).elim

def originalRawGammaTotalBijection
    (h00 : M ⊨ Axioms.ACVF00)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (D : GammaDomainFormula B p n (fun _ => .rv))
    (hD : ∀ x : X, originalGammaSourceValid hc D (rvValues x.val)) :
    GammaGroundBijection (originalRVTotalFamily X D)
      (rawRVGammaLift h00 X (originalRawGammaFamily X D hD)) :=
  (rawGammaRepresentativeBijection h00 X (originalRawGammaFamily X D hD)).comp
    ((gammaGroundBijectionOfCarrierEq _ _ (originalRawGammaTotal_preimage h00 X D hD)).comp
      ((rawGammaTotalPacking (n := n) X).restrictTarget (originalRVTotalFamily X D)
        (originalRVTotalFamily_subset_gamma_packing X D hD)).symm)

end DiamondIntegral.Section5
