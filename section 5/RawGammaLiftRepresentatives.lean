import «section 5».RawRVGammaFamilies
import «section 5».RawRVUnitPartitions
import «section 3».RVUnitTupleProducts

/-! The coded raw-base lift is actually bijective to the full family of
all RV representatives over the original raw RV base, including zeros. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p n : ℕ}

theorem rawRVGammaLift_row (h00 : M ⊨ Axioms.ACVF00)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (T : GammaGroundDefSet hc B ((rawRVSpace (M := M) p).prod ((volumeGammaSpace hc).power (Fin n))))
    (x : X) (z : Fin n → (CanonicalRV.RVSort M)ˣ) :
    Fin.append (rvNonzeroTupleCode x.val) z ∈ (rawRVGammaLift h00 X T).carrier ↔
      (x.val,rvUnitTupleValues z) ∈ T.carrier := by
  let e := gammaGroundRVNonzeroTupleCodeBijection h00 X
  let q := e.map x
  have hl : Fin.append (rvNonzeroTupleCode x.val) z ∘ Fin.castAdd n = q.val := by
    funext j
    exact Fin.append_left _ _ j
  have hr : Fin.append (rvNonzeroTupleCode x.val) z ∘ Fin.natAdd (p*2) = z := by
    funext j
    exact Fin.append_right _ _ j
  change (_,_ ) ∈ (rawRVGammaFamilyCode h00 X T).carrier ↔ _
  rw [hl,hr]
  refine (rawRVGammaFamilyCode_row h00 X T q (rvUnitTupleValues z)).trans ?_
  have he : e.symm.map q = x := GammaGroundMap.inverse_apply _ _ x
  exact Iff.of_eq (congrArg (fun a : X => (a.val,rvUnitTupleValues z) ∈ T.carrier) he)

def rawGammaLiftPacking (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p)) :=
  gammaGroundRVUnitTupleProductBijection
    ((rawRVGammaBaseCode X).prod (GammaGroundDefSet.univ hc B (rawRVUnitSpace (M := M) n)))

theorem rawGammaLift_subset_packing (h00 : M ⊨ Axioms.ACVF00)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (T : GammaGroundDefSet hc B ((rawRVSpace (M := M) p).prod ((volumeGammaSpace hc).power (Fin n)))) :
    (rawRVGammaLift h00 X T).carrier ⊆
      (gammaGroundRVUnitTupleProductMap
        ((rawRVGammaBaseCode X).prod (GammaGroundDefSet.univ hc B (rawRVUnitSpace (M := M) n)))).image.carrier := by
  intro u hu
  have hx : u ∘ Fin.castAdd n ∈ (rawRVGammaBaseCode X).carrier :=
    rawRVGammaFamilyCode_projection h00 X T _ _ hu
  refine ⟨⟨(u ∘ Fin.castAdd n,u ∘ Fin.natAdd (p*2)),hx,Set.mem_univ _⟩,?_⟩
  change Fin.append (u ∘ Fin.castAdd n) (u ∘ Fin.natAdd (p*2)) = u
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp only [Fin.append_left,Fin.append_right,Function.comp_def]

def rawGammaRepresentativeBaseBijection (h00 : M ⊨ Axioms.ACVF00)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p)) :=
  (gammaGroundRVNonzeroTupleCodeBijection h00 X).prodMap
    (GammaGroundBijection.id (GammaGroundDefSet.univ hc B (rawRVUnitSpace (M := M) n)))

def rawGammaRepresentativeDomain (h00 : M ⊨ Axioms.ACVF00)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (T : GammaGroundDefSet hc B ((rawRVSpace (M := M) p).prod ((volumeGammaSpace hc).power (Fin n)))) :=
  (rawGammaRepresentativeBaseBijection (n := n) h00 X).inverseImage
    ((rawGammaLiftPacking (n := n) X).inverseImage (rawRVGammaLift h00 X T))

def rawGammaRepresentativeBijection (h00 : M ⊨ Axioms.ACVF00)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (T : GammaGroundDefSet hc B ((rawRVSpace (M := M) p).prod ((volumeGammaSpace hc).power (Fin n)))) :
    GammaGroundBijection (rawGammaRepresentativeDomain h00 X T) (rawRVGammaLift h00 X T) :=
  ((rawGammaLiftPacking (n := n) X).restrictTarget (rawRVGammaLift h00 X T)
    (rawGammaLift_subset_packing h00 X T)).comp
      ((rawGammaRepresentativeBaseBijection (n := n) h00 X).restrictTarget
        ((rawGammaLiftPacking (n := n) X).inverseImage (rawRVGammaLift h00 X T))
        ((rawGammaLiftPacking (n := n) X).inverseImage_subset (rawRVGammaLift h00 X T)))

theorem rawGammaRepresentativeDomain_row (h00 : M ⊨ Axioms.ACVF00)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (T : GammaGroundDefSet hc B ((rawRVSpace (M := M) p).prod ((volumeGammaSpace hc).power (Fin n))))
    (x : X) (z : Fin n → (CanonicalRV.RVSort M)ˣ) :
    (x.val,z) ∈ (rawGammaRepresentativeDomain h00 X T).carrier ↔ (x.val,rvUnitTupleValues z) ∈ T.carrier := by
  let a : X.prod (GammaGroundDefSet.univ hc B (rawRVUnitSpace (M := M) n)) := ⟨(x.val,z),x.property,Set.mem_univ _⟩
  have h1 := groundBijection_inverseImage_at (rawGammaRepresentativeBaseBijection (n := n) h00 X)
    ((rawGammaLiftPacking (n := n) X).inverseImage (rawRVGammaLift h00 X T)) a
  have h2 := groundBijection_inverseImage_at (rawGammaLiftPacking (n := n) X)
    (rawRVGammaLift h00 X T) ((rawGammaRepresentativeBaseBijection (n := n) h00 X).map a)
  exact h1.trans (h2.trans (rawRVGammaLift_row h00 X T x z))

end DiamondIntegral.Section5
