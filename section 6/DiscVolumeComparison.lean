import IntegrationSection2.ConstructedGaussGraph
import Section9.GammaPolydiscDescent

/-! Constant-Jacobian comparison on actual RV polydiscs. The former Gauss
graph input is supplied by the checked Integration in ACVF construction;
no field-theoretic reference premise is added. This is the local volume
calculation needed in unary matching, not the whole matching construction. -/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7
open SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section6

variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] {n r s : ℕ} {S : Set M}

theorem polydisc_volume_comparison [CharZero (VFType (M := M))]
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk S < κ) (v : Valuation (VFType (M := M)) G)
    (hv : ∀ a b : VFType (M := M), VFValued.predV a b ↔ v a ≤ v b)
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    {B : DefSet (rawMixedSpace (M := M) n s) S}
    (f : Map A B) (hf : Function.Bijective f) (a b : Fin n → VFType (M := M))
    (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    (hA : ∀ x, (∃ p : A, p.val.1 = x) ↔
      x ∈ RVFibre v (fun i => RVCalc.rv v (a i)))
    (hB : ∀ x, (∃ p : B, p.val.1 = x) ↔
      x ∈ RVFibre v (fun i => RVCalc.rv v (b i)))
    (c : VFType (M := M)) (hc₀ : c ≠ 0)
    (Z : DefSet (rawMixedSpace (M := M) n r) S)
    (hZ : vfDim (rawRVSpace (M := M) 1) Z < n)
    (hconst : ∀ p : A, p.val ∉ Z.carrier →
      ∃ J, HasMixedVFJacobianAt f p J ∧ v J = v c) :
    v c = (∏ i, v (b i)) / ∏ i, v (a i) :=
  gammaDescent_polydiscs_of_vfSmall_exception hc hκ hs h00 hsmall v hv f hf
    a b ha hb hA hB c hc₀ Z hZ hconst
    IntegrationInACVF.Section2.ConstructedGaussGraph.acvf_graph_input

theorem unary_disc_volume_comparison [CharZero (VFType (M := M))]
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk S < κ) (v : Valuation (VFType (M := M)) G)
    (hv : ∀ a b : VFType (M := M), VFValued.predV a b ↔ v a ≤ v b)
    {A : DefSet (rawMixedSpace (M := M) 1 r) S}
    {B : DefSet (rawMixedSpace (M := M) 1 s) S}
    (f : Map A B) (hf : Function.Bijective f) (a b : VFType (M := M))
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hA : ∀ x, (∃ p : A, p.val.1 = x) ↔
      x ∈ RVFibre v (fun _ => RVCalc.rv v a))
    (hB : ∀ x, (∃ p : B, p.val.1 = x) ↔
      x ∈ RVFibre v (fun _ => RVCalc.rv v b))
    (c : VFType (M := M)) (hc₀ : c ≠ 0)
    (Z : DefSet (rawMixedSpace (M := M) 1 r) S)
    (hZ : vfDim (rawRVSpace (M := M) 1) Z < 1)
    (hconst : ∀ p : A, p.val ∉ Z.carrier →
      ∃ J, HasMixedVFJacobianAt f p J ∧ v J = v c) : v c = v b / v a := by
  simpa only [Fin.prod_univ_one] using
    polydisc_volume_comparison hc hκ hs h00 hsmall v hv f hf
      (fun _ => a) (fun _ => b) (fun _ => ha) (fun _ => hb) hA hB c hc₀ Z hZ hconst

end DiamondIntegral.Section6
