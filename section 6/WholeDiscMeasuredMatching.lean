import «section 6».NamedTagFibres
import Section4.ParameterInvariance

/-! The measured adapter for an actually prepared unary disc matching.
Every whole old-tag fiber is an actual full RV disc. Its restricted map
has the ambient Jacobian value away from the original VF-small locus,
so centered-disc descent gives the radius identity at every label. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7
open SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {r s : ℕ} {S : Set M}

theorem prepared_unary_matching_volume_identity [CharZero (VF M)]
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) 1 r) S}
    {B : DefSet (rawMixedSpace (M := M) 1 s) S}
    (f : Map A B) (hf : Function.Injective f) (hWhole : MapsWholeTagFibres f)
    (hA : ProperInvariant S A.carrier) (hAD : VFDoublyBounded A.carrier) (hARV : IsRVPullback A.carrier)
    (hATag : ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1)
    (hBD : VFDoublyBounded B.carrier) (hBRV : IsRVPullback B.carrier)
    (hBTag : ∀ p ∈ B.carrier, ∀ q ∈ B.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1)
    (ω : Mixed M 1 r → Gamma M) (σ : Mixed M 1 s → Gamma M)
    (hω : ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → ω p = ω q)
    (hσ : ∀ p ∈ B.carrier, ∀ q ∈ B.carrier, p.2 = q.2 → σ p = σ q)
    (Z : DefSet (rawMixedSpace (M := M) 1 r) S)
    (hZ : vfDim (rawRVSpace (M := M) 1) Z < 1)
    (hconst : ∀ p : A, p.val ∉ Z.carrier →
      ∃ J, HasMixedVFJacobianAt f p J ∧ vfValue J = (ω p.val / σ (f p).val).val)
    (p : A) :
    ω p.val * finiteValue (p.val.1 0) (hAD.nonzero p.property 0) =
      σ (f p).val * finiteValue ((f p).val.1 0) (hBD.nonzero (f p).property 0) := by
  let T := S ∪ Set.range (rvValues p.val.2)
  have hST : S ⊆ T := Set.subset_union_left
  have hT : Cardinal.mk T < κ := small_union_finite hκ.le S hsmall _ (Set.finite_range _)
  let A' := A.extend hST
  let B' := B.extend hST
  let f' : Map A' B' := f.extend hST
  let p' : A' := p
  have hu (i : Fin r) : (p.val.2 i).val ∈ T := Or.inr (Set.mem_range_self i)
  let C := namedTagFiber A' p.val.2 hu
  have hCA : C.carrier ⊆ A'.carrier := namedTagFiber_subset A' p.val.2 hu
  have hp0 := hAD.nonzero p.property 0
  have hfp0 := hBD.nonzero (f p).property 0
  have hC (x : Fin 1 → VF M) : (∃ q : C, q.val.1 = x) ↔
      x 0 ∈ centeredGammaDisc (p.val.1 0) (finiteValue (p.val.1 0) hp0) := by
    rw [namedTagFiber_projection]
    exact Set.ext_iff.mp (unary_tag_fiber_eq_centered_disc A hARV hAD hATag p) x
  have hImage (x : Fin 1 → VF M) : (∃ q : (f'.restrict hCA).image, q.val.1 = x) ↔
      x 0 ∈ centeredGammaDisc ((f p).val.1 0) (finiteValue ((f p).val.1 0) hfp0) := by
    rw [namedTagFiber_image_projection f' hWhole p' hu]
    exact Set.ext_iff.mp (unary_tag_fiber_eq_centered_disc B hBRV hBD hBTag (f p)) x
  have hOpen := namedTagFiber_open A' (fun u => (hA.clopen_fibres hv u).isOpen) p.val.2 hu
  have hZ' : vfDim (rawRVSpace (M := M) 1) (Z.extend hST) < 1 :=
    (vfDim_extend_le _ hST Z).trans_lt hZ
  have hConstant (q : A') (hq : q.val ∈ C.carrier) (hqZ : q.val ∉ (Z.extend hST).carrier) :
      ∃ J, HasMixedVFJacobianAt f' q J ∧ vfValue J = (ω p.val/σ (f p).val).val := by
    obtain ⟨J,hJ,hVal⟩ := hconst q hqZ
    have hωq := hω q.val q.property p.val p.property hq.2
    have hTags := hWhole.labels f q p hq.2
    have hσq := hσ (f q).val (f q).property (f p).val (f p).property hTags
    rw [hωq,hσq] at hVal
    exact ⟨J,hJ,hVal⟩
  exact literal_paired_core_volume_identity hc hκ hs h00 hT hv f' hf hCA hOpen
    (p.val.1 0) ((f p).val.1 0) (finiteValue _ hp0) (finiteValue _ hfp0) (ω p.val) (σ (f p).val)
    hC hImage (Z.extend hST) hZ' hConstant

end DiamondIntegral.Section6
