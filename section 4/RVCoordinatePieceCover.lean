import Section4.RVDimensionRank
import Section4.UniformFinite

/-! Expose the finite coordinate-piece cover used in the dimension/rank
proof, and give a uniform numerical bound on each piece's fibres. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section4.RVCoordinatePieceCover
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem exists_cover (hc : CanonicalStructure.IsCanonical (M := M))
    (hex : RVExchangeInput (M := M)) {κ : Cardinal} (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ) {n k : ℕ}
    (A : DefSet (rawRVSpace (M := M) n) S) (hdim : rvDim A ≤ k) :
    ∃ m : ℕ, ∃ D : Fin m → RVCoordinatePiece (M := M) S n k,
      ∀ a ∈ A.carrier, ∃ i, a ∈ (D i).source.carrier := by
  let P := rawRVSpace (M := M) n
  let Data := RVCoordinatePiece (M := M) S n k
  let U (D : Data) := P.preimage D.source.carrier
  have hcover : ∀ z ∈ P.preimage A.carrier, ∃ c ∈ Set.range U, z ∈ c := by
    rintro z ⟨hz, ha⟩
    let a : A := ⟨P.decode ⟨z, hz⟩, ha⟩
    obtain ⟨v, hv⟩ := exists_rv_coordinate_basis hc hex S a.val
    obtain ⟨D, hD⟩ := rv_coordinate_piece_of_algebraic
      ((rvTupleRank_le_rvDim hc hex A a).trans hdim) v a.val
      (fun j => (hv j).raw_finite_witness)
    exact ⟨U D, Set.mem_range_self D, hz, hD⟩
  obtain ⟨C, hC, hsub, hcov⟩ := definable_finite_subcover_index hs S hsmall
    (P.preimage A.carrier) A.definable (Set.range U)
    (by rintro _ ⟨D, rfl⟩; exact D.source.definable) hcover
  letI : Fintype C := hC.fintype
  have hchoice (c : C) : ∃ D : Data, U D = c.val := hsub c.property
  let D (c : C) : Data := Classical.choose (hchoice c)
  have hD (c : C) : U (D c) = c.val := Classical.choose_spec (hchoice c)
  let e := Fintype.equivFin C
  refine ⟨Fintype.card C, fun i => D (e.symm i), ?_⟩
  intro a ha
  have hraw : rvValues a ∈ P.preimage A.carrier :=
    ⟨⟨a, rfl⟩, by simpa only [P, decode_rvValues] using ha⟩
  obtain ⟨c, hc, hac⟩ := hcov _ hraw
  let c' : C := ⟨c, hc⟩
  refine ⟨e c', ?_⟩
  simp only [Equiv.symm_apply_apply]
  have hac' := (Set.ext_iff.mp (hD c') (rvValues a)).mpr hac
  have hmem := (P.preimage_decode (D c').source.carrier
    ⟨rvValues a, ⟨a, rfl⟩⟩).mp hac'
  simpa only [P, decode_rvValues] using hmem

theorem uniform_bound {κ : Cardinal} (hs : Saturated M κ) {S : Set M}
    (hsmall : Cardinal.mk S < κ) {n k : ℕ} (D : RVCoordinatePiece (M := M) S n k) :
    ∃ C : ℕ, ∀ y : Fin D.arity → CanonicalRV.RVSort M,
      {a ∈ D.source.carrier | a ∘ D.select = y}.Finite ∧
      {a ∈ D.source.carrier | a ∘ D.select = y}.ncard ≤ C := by
  have hN (j : Fin n) := uniform_finite_fibre_bound hs S hsmall
    (D.relation j).val (D.relation j).property.1 (D.relation j).property.2
  choose N hN using hN
  refine ⟨∏ j, N j, ?_⟩
  intro y
  let H : Set (Fin n → M) := {x | ∀ j, (rvValues y, x j) ∈ (D.relation j).val}
  have hH : H.Finite := Set.Finite.pi' (fun j => (D.relation j).property.2 (rvValues y))
  have hmaps : ∀ a ∈ {a ∈ D.source.carrier | a ∘ D.select = y}, rvValues a ∈ H := by
    rintro a ⟨ha, he⟩ j
    have hj := ha j
    change (rvValues (a ∘ D.select), (a j).val) ∈ (D.relation j).val at hj
    rwa [he] at hj
  have hfin := (hH.preimage rvValues_injective.injOn).subset hmaps
  refine ⟨hfin, (Set.ncard_le_ncard_of_injOn rvValues hmaps rvValues_injective.injOn hH).trans ?_⟩
  let e : H ≃ (∀ j : Fin n, {x : M // (rvValues y, x) ∈ (D.relation j).val}) := {
    toFun x j := ⟨x.val j, x.property j⟩
    invFun x := ⟨fun j => (x j).val, fun j => (x j).property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  change Nat.card H ≤ _
  rw [Nat.card_congr e, Nat.card_pi]
  exact Finset.prod_le_prod (fun j _ => hN j (rvValues y))

end DiamondIntegral.Section4.RVCoordinatePieceCover
