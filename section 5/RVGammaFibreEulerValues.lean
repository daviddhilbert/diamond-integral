import «section 5».RVGammaFamilySchemata
import «section 5».OriginalEulerValueConstructibility

/-! Actual original-ground RV/Gamma families have constructible Gamma
fibre Euler values computed over the exact displayed RV parameter base. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4 GammaOrderLogic
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p n : ℕ}

theorem rvGammaFamily_row_definable
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) p).prod ((volumeGammaSpace hc).power (Fin n))))
    (x : Fin p → (CanonicalRV.RVSort M)ˣ) :
    GammaDefinable ⟨B.real ∪ Set.range (rvUnitValues x), B.gamma⟩ {γ | (x,γ) ∈ T.carrier} := by
  convert originalGammaSourceRow_definable hc (rvGammaFamilySchema T) (rvUnitValues x)
    (rvGammaFamilySchema_valid T x) using 1
  exact (rvGammaFamilySchema_quotient_row T x).symm

def rvGammaFibreEulerValue (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) p).prod ((volumeGammaSpace hc).power (Fin n))))
    (x : Fin p → (CanonicalRV.RVSort M)ˣ) (kind : EulerKind) : ℤ :=
  originalGammaRowEulerValue hc h00 hκ hs hr hγ (rvGammaFamilySchema T) (rvUnitValues x) kind

theorem rvGammaFibreEulerValue_integral (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) p).prod ((volumeGammaSpace hc).power (Fin n))))
    (x : Fin p → (CanonicalRV.RVSort M)ˣ) (kind : EulerKind) :
    rvGammaFibreEulerValue hc h00 hκ hs hr hγ T x kind =
      GammaIteratedIntegral.integrateAll h00 hκ hs ⟨B.real ∪ Set.range (rvUnitValues x), B.gamma⟩
        (small_union_range_carrier hκ B.real hr (rvUnitValues x)) hγ kind n
        (GammaIndicators.indicatorFamily _ {γ | (x,γ) ∈ T.carrier} (rvGammaFamily_row_definable T x)) := by
  unfold rvGammaFibreEulerValue originalGammaRowEulerValue
  rw [dif_pos (rvGammaFamilySchema_valid T x)]
  apply congrArg
    (GammaIteratedIntegral.integrateAll h00 hκ hs ⟨B.real ∪ Set.range (rvUnitValues x), B.gamma⟩
      (small_union_range_carrier hκ B.real hr (rvUnitValues x)) hγ kind n)
  apply Subtype.ext
  funext γ
  change (if γ ∈ originalGammaSourceRow hc (rvGammaFamilySchema T) (rvUnitValues x) then (1 : ℤ) else 0) = _
  rw [rvGammaFamilySchema_quotient_row T x]
  rfl

theorem rv_gamma_fibre_euler_constructible (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) p))
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) p).prod ((volumeGammaSpace hc).power (Fin n))))
    (kind : EulerKind) :
    (Set.range (fun x : X => rvGammaFibreEulerValue hc h00 hκ hs hr hγ T x.val kind)).Finite ∧
      ∀ m : ℤ, GammaGroundDefinable hc B (rawRVUnitSpace (M := M) p)
        {x | x ∈ X.carrier ∧ rvGammaFibreEulerValue hc h00 hκ hs hr hγ T x kind = m} := by
  let A := rvUnitValues '' X.carrier
  have hA : DefinableOverBase B (fun _ : Fin p => .rv) A :=
    (gammaGroundRVUnit_definable_iff X.carrier).mp X.definable
  have hD : ∀ z ∈ A, originalGammaSourceValid hc (rvGammaFamilySchema T) z := by
    rintro z ⟨x, hx, rfl⟩
    exact rvGammaFamilySchema_valid T x
  obtain ⟨hfinite, hlevels⟩ := original_euler_row_values_constructible hc h00 hκ hs hr hγ A hA
    (rvGammaFamilySchema T) hD kind
  constructor
  · apply hfinite.subset
    rintro m ⟨x, rfl⟩
    exact ⟨⟨rvUnitValues x.val, x.val, x.property, rfl⟩, rfl⟩
  · intro m
    apply (gammaGroundRVUnit_definable_iff _).mpr
    convert hlevels m using 1
    ext z
    constructor
    · rintro ⟨x, ⟨hx, hm⟩, hz⟩
      change originalGammaRowEulerValue hc h00 hκ hs hr hγ (rvGammaFamilySchema T) (rvUnitValues x) kind = m at hm
      exact ⟨⟨x, hx, hz⟩, hz ▸ hm⟩
    · rintro ⟨⟨x, hx, hz⟩, hm⟩
      refine ⟨x, ⟨hx, ?_⟩, hz⟩
      change originalGammaRowEulerValue hc h00 hκ hs hr hγ (rvGammaFamilySchema T) (rvUnitValues x) kind = m
      rwa [hz]

end DiamondIntegral.Section5
