import «section 5».GeometricPaddedRVRows
import «section 5».OriginalProductTotalBijections
import «section 5».NativeRVSetArithmetic

/-! Literal affine padding of an RV family is an actual cartesian product
of its whole RV total with the original-ground padding domain. Consequently
the total raw value receives precisely the original-ground affine power. -/
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
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVCodeBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a b : ℕ}

theorem nativeRVProductDomain_append_mem
    (A : GammaGroundDefSet hc B (rawRVSpace (M := M) a))
    (C : GammaGroundDefSet hc B (rawRVSpace (M := M) b))
    (x : Fin a → CanonicalRV.RVSort M) (y : Fin b → CanonicalRV.RVSort M) :
    Fin.append x y ∈ (gammaGroundRVProductDomain A C).carrier ↔ x ∈ A.carrier ∧ y ∈ C.carrier := by
  rw [←rvValues_mem_rawDomain_iff,rawDomain_product,rvValues_append]
  have hl : Fin.append (rvValues x) (rvValues y) ∘ Fin.castAdd b = rvValues x :=
    funext (fun i => Fin.append_left _ _ i)
  have hr : Fin.append (rvValues x) (rvValues y) ∘ Fin.natAdd a = rvValues y :=
    funext (fun i => Fin.append_right _ _ i)
  rw [hl,hr,rvValues_mem_rawDomain_iff,rvValues_mem_rawDomain_iff]

theorem originalConstantProductTotal_reindex
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (D : GammaDomainFormula B p a (fun _ => .rv))
    (Q : GammaGroundDefSet hc B (rawRVSpace (M := M) b))
    (u : Fin (p+(a+b)) → CanonicalRV.RVSort M) :
    u ∈ (originalRVTotalFamily X (originalDomainProduct D (originalConstantRVDomain Q (fun _ => .rv)))).carrier ↔
      u ∘ finCongr (Nat.add_assoc p a b) ∈ (gammaGroundRVProductDomain (originalRVTotalFamily X D) Q).carrier := by
  let x := u ∘ Fin.castAdd (a+b)
  let y := (u ∘ Fin.natAdd p) ∘ Fin.castAdd b
  let z := (u ∘ Fin.natAdd p) ∘ Fin.natAdd a
  have hpack : Fin.append x (Fin.append y z) = u := by
    dsimp only [x,y,z]
    have ht : Fin.append ((u ∘ Fin.natAdd p) ∘ Fin.castAdd b)
        ((u ∘ Fin.natAdd p) ∘ Fin.natAdd a) = u ∘ Fin.natAdd p := Fin.append_castAdd_natAdd
    exact (congrArg (Fin.append (u ∘ Fin.castAdd (a+b))) ht).trans Fin.append_castAdd_natAdd
  have hassoc : Fin.append x (Fin.append y z) ∘ finCongr (Nat.add_assoc p a b) =
      Fin.append (Fin.append x y) z := (Fin.append_assoc x y z).symm
  rw [←hpack,hassoc,originalRVTotalFamily_append_mem,nativeRVProductDomain_append_mem,
    originalRVTotalFamily_append_mem,originalDomainProduct_row]
  have hy : Fin.append (rvValues y) (rvValues z) ∘ Fin.castAdd b = rvValues y :=
    funext (fun i => Fin.append_left _ _ i)
  have hz : Fin.append (rvValues y) (rvValues z) ∘ Fin.natAdd a = rvValues z :=
    funext (fun i => Fin.append_right _ _ i)
  rw [rvValues_append,hy,hz,
    originalConstantRVDomain_row Q (fun _ : Fin p => .rv) (rvValues x) (fun i => (x i).property),
    rvValues_mem_rawDomain_iff]
  exact and_assoc.symm

def originalConstantProductTotalBijection
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (D : GammaDomainFormula B p a (fun _ => .rv))
    (Q : GammaGroundDefSet hc B (rawRVSpace (M := M) b)) :
    GammaGroundBijection (originalRVTotalFamily X (originalDomainProduct D (originalConstantRVDomain Q (fun _ => .rv))))
      (gammaGroundRVProductDomain (originalRVTotalFamily X D) Q) :=
  rawTupleReindexBijection _ _ (finCongr (Nat.add_assoc p a b)) (originalConstantProductTotal_reindex X D Q)

theorem nativePaddedRV_total_value
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (D : GammaDomainFormula B p a (fun _ => .rv)) (r : ℕ) :
    nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (originalRVTotalFamily X (originalPaddedRVDomain hc D r)) =
      nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (originalRVTotalFamily X D) *
        RESAffineLocalization.dimensionFreeAffine B ^ r := by
  have he := nativeRVSetValue_bijection h00 linear hκ hs hc B hr hγ hΓ kind _ _
    (originalConstantProductTotalBijection X D (nativeAffineRVPower hc B r).domain)
  refine he.trans ?_
  rw [nativeRVSetValue_product,nativeRVSetValue_object,nativeAffineRVPower_raw_value]

end DiamondIntegral.Section5
