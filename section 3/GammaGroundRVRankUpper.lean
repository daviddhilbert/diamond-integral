import «section 3».GammaGroundRealization
import «section 3».GammaGroundFiniteGluing
import Section4.RVDimensionRank
import Section4.GammaRVIndependence
import Section3.GammaProjection
import «section 3».GammaGroundRealFibres
import «section 3».GammaGroundMapImages
import «section 3».GammaGroundRawDescent
import «section 3».GammaGroundSyntaxBridge
import Section4.RelationFibres
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {P Q : Space LRV M}
variable {n k : ℕ}
theorem gammaGroundRVFiniteMap_of_coordinate_algebraicity
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hS : Cardinal.mk ground.real < κ)
    (A : GammaGroundDefSet hc ground (rawRVSpace (M := M) n)) (k : ℕ)
    (halg : ∀ a : A, ∃ d ≤ k, ∃ v : Fin d → Fin n,
      ∀ j, RawClosure.AlgebraicOver (ground.real ∪ Set.range (rvValues (a.val ∘ v))) (a.val j).val) :
    ∃ f : GammaGroundMap A (GammaGroundDefSet.univ hc ground (rawRVSpace (M := M) k)), f.FiniteFibres := by
  let P := rawRVSpace (M := M) n
  let Data := RVCoordinatePiece (M := M) ground.real n k
  let U (D : Data) := P.preimage D.source.carrier
  obtain ⟨T, hT, hsmall, _, hA⟩ := A.definable.realize hκ hS
  have hU (D : Data) : T.Definable LRV (U D) := D.source.definable.mono _ hT
  have hcover : ∀ z ∈ P.preimage A.carrier, ∃ c ∈ Set.range U, z ∈ c := by
    rintro z ⟨hz, ha⟩
    let a : A := ⟨P.decode ⟨z, hz⟩, ha⟩
    obtain ⟨d, hd, v, hv⟩ := halg a
    obtain ⟨D, hD⟩ := rv_coordinate_piece_of_algebraic hd v a.val hv
    exact ⟨U D, Set.mem_range_self D, hz, hD⟩
  obtain ⟨C, hC, hsub, hcov⟩ := definable_finite_subcover_index hs T hsmall
    (P.preimage A.carrier) hA (Set.range U)
    (by rintro _ ⟨D, rfl⟩; exact hU D) hcover
  letI : Fintype C := hC.fintype
  have hchoice (c : C) : ∃ D : Data, U D = c.val := hsub c.property
  let D (c : C) : Data := Classical.choose (hchoice c)
  have hD (c : C) : U (D c) = c.val := Classical.choose_spec (hchoice c)
  let B := GammaGroundDefSet.univ hc ground (rawRVSpace (M := M) k)
  let E (c : C) := GammaGroundDefSet.ofReal (hc := hc) (ground := ground) (D c).source
  have hcover' : ∀ a : A, ∃ c : C, a.val ∈ (E c).carrier := by
    intro a
    have ha : rvValues a.val ∈ P.preimage A.carrier :=
      ⟨⟨a.val, rfl⟩, by simpa only [P, decode_rvValues] using a.property⟩
    obtain ⟨c, hc', hac⟩ := hcov _ ha
    let c' : C := ⟨c, hc'⟩
    refine ⟨c', ?_⟩
    have hac' := (Set.ext_iff.mp (hD c') (rvValues a.val)).mpr hac
    have hmem := (P.preimage_decode (D c').source.carrier
      ⟨rvValues a.val, ⟨a.val, rfl⟩⟩).mp hac'
    simpa only [E, GammaGroundDefSet.ofReal, P, decode_rvValues] using hmem
  let f (c : C) : GammaGroundMap (E c) B := GammaGroundMap.ofReal (D c).paddedProjection
  have hf (c : C) : (f c).FiniteFibres := (D c).paddedProjection_finite
  exact gammaGroundFiniteCoverFiniteMap A B E f hf hcover'

theorem gammaGroundRVFiniteMap_of_point_rank
    (hex : RVExchangeInput (M := M)) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hS : Cardinal.mk ground.real < κ)
    (A : GammaGroundDefSet hc ground (rawRVSpace (M := M) n)) (k : ℕ)
    (hrank : ∀ a : A, rvTupleRank hc hex ground.real a.val ≤ k) :
    ∃ f : GammaGroundMap A (GammaGroundDefSet.univ hc ground (rawRVSpace (M := M) k)), f.FiniteFibres := by
  apply gammaGroundRVFiniteMap_of_coordinate_algebraicity hκ hs hS A k
  intro a
  obtain ⟨v, hv⟩ := exists_rv_coordinate_basis hc hex ground.real a.val
  exact ⟨rvTupleRank hc hex ground.real a.val, hrank a, v,
    fun j => (hv j).raw_finite_witness⟩

end DiamondIntegral.Section3
