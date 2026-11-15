import «section 5».OriginalRVTotalGraphs

/-! Totalizing an original bijective row graph preserves the full raw
RV parameter tuple literally, as required by relative family products. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVCodeBridge FiniteTupleBlocks
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a b : ℕ}

theorem rawEquivalenceBijection_value (A : Set (Fin a → M)) (C : Set (Fin b → M))
    (hA : DefinableOverBase B (fun _ => .rv) A)
    (hC : DefinableOverBase B (fun _ => .rv) C) (e : A ≃ C)
    (hg : DefinableOverBase B (fun _ : Fin (b+a) => .rv)
      {w | ∃ u : A, w = join b a u.val (e u).val}) (u : ofRaw (hc := hc) A hA) :
    rvValues ((rawEquivalenceBijection A C hA hC e hg).map u).val =
      (e ⟨rvValues u.val,u.property⟩).val := by
  change (if h : rvValues u.val ∈ A then (e ⟨rvValues u.val,h⟩).val else fun _ => iRVZero) = _
  exact dif_pos (show rvValues u.val ∈ A from u.property)

theorem originalRVTotalBijection_preserves_base
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (D : GammaDomainFormula B p a (fun _ => .rv))
    (E : GammaDomainFormula B p b (fun _ => .rv))
    (H : GammaRelationFormula B p a b (fun _ => .rv))
    (hv : ∀ x : X, bijectiveMapRowValid (fun _ => .rv) (fun _ : Fin b => .rv)
      D.val E.val H.val (rvValues x.val)) (u : originalRVTotalFamily X D) :
    ((originalRVTotalBijection X D E H hv).map u).val ∘ Fin.castAdd b = u.val ∘ Fin.castAdd a := by
  have hraw : ∀ z ∈ rawDomain X, bijectiveMapRowValid (fun _ => .rv) (fun _ : Fin b => .rv)
      D.val E.val H.val z := by
    rintro z ⟨x,hx,rfl⟩
    exact hv ⟨x,hx⟩
  let A := rawRowTotal (rawDomain X) D.val
  let C := rawRowTotal (rawDomain X) E.val
  let t : ofRaw (hc := hc) A (rawRowTotal_definable X D) := ⟨u.val,u.property.2,u.property.1⟩
  have he := rawEquivalenceBijection_value A C (rawRowTotal_definable X D) (rawRowTotal_definable X E)
    (originalRawTotalEquiv (rawDomain X) D E H hraw)
    (originalRawTotalEquiv_joined_definable X D E H hraw) t
  have hsame : rvValues ((originalRVTotalBijection X D E H hv).map u).val =
      rvValues ((rawEquivalenceBijection (hc := hc) A C (rawRowTotal_definable X D)
        (rawRowTotal_definable X E) (originalRawTotalEquiv (rawDomain X) D E H hraw)
        (originalRawTotalEquiv_joined_definable X D E H hraw)).map t).val := rfl
  apply rvValues_injective
  change rvValues ((originalRVTotalBijection X D E H hv).map u).val ∘ Fin.castAdd b =
    rvValues u.val ∘ Fin.castAdd a
  rw [hsame,he,originalRawTotalEquiv_value]
  funext j
  exact Fin.append_left _ _ j

end DiamondIntegral.Section5
