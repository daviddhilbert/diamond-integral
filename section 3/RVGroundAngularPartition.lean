import «section 3».RVGroundValuePatterns
import «section 3».RVAngularPartition
import «section 3».RVUnitDomains
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GuardedRVNormalForm
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

theorem gammaSyntax_decode_rvUnitValues (x : Fin n → (CanonicalRV.RVSort M)ˣ) :
    GammaSyntax.decode (rvUnitValues x) = rvUnitTupleValues x := by
  funext i
  exact codeValue_raw ⟨(x i).val,fun h => Units.ne_zero (x i) (Subtype.ext (h.trans RVOperations.zero_val.symm))⟩

theorem rvUnitValues_gammaProper (x : Fin n → (CanonicalRV.RVSort M)ˣ) :
    GammaSyntax.Proper (rvUnitValues x) := fun i =>
  ⟨(x i).val.property,fun h => Units.ne_zero (x i) (Subtype.ext (h.trans RVOperations.zero_val.symm))⟩

/-- The finite disjoint angular partition descends from a proof-only
common-name normal form to the original real/Gamma parameter base. -/
theorem gammaGround_finite_angular_partition {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (A : Set (Fin n → M)) (hA : DefinableOverBase B (fun _ => .rv) A) :
    ∃ N : ℕ, ∃ X : Fin N → Set (Fin n → M),
      (∀ i, DefinableOverBase B (fun _ => .rv) (X i)) ∧
      (∀ i, Nonempty (RVAngularCell {x | rvUnitValues x ∈ X i})) ∧
      (∀ i j, i ≠ j → Disjoint (X i) (X j)) ∧
      ∀ x : Fin n → (CanonicalRV.RVSort M)ˣ, rvUnitValues x ∈ A ↔ ∃ i, rvUnitValues x ∈ X i := by
  obtain ⟨p,D,hD⟩ := definableRV_guarded_DNF hA.common_names
  let J := RVDNFGlobalPattern D
  letI := Fintype.ofFinite J
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  let C := rvDNFPatternCell D (sourceVFFixedValues p n) (sourceRVFixedParameters p)
  let X : Fin (Fintype.card J) → Set (Fin n → M) := fun i => rvUnitValues '' C (e i)
  have hmatch : ∀ x : Fin n → (CanonicalRV.RVSort M)ˣ, rvUnitValues x ∈ A ↔
      PolarityDNF.holds (RVLiteral.comparison (sourceVFFixedValues p n) (sourceRVFixedParameters p)
        (fun i => (x i : CanonicalRV.RVSort M))) D := fun x => (hD x).1
  have hX : ∀ i, DefinableOverBase B (fun _ => .rv) (X i) := by
    intro i
    have hp := globalGammaPattern_definable hκ hs h00 hc B hsmall p D (e i)
    have hh := FullBaseAtomicity.OverBase.inter (integrationGammaDefinable hA) hp
    have he : X i = {z | z ∈ A ∧ GammaSyntax.Proper z ∧
        globalGammaPattern D (sourceVFFixedValues p n) (sourceRVFixedParameters p) (e i) (GammaSyntax.decode z)} := by
      ext z
      constructor
      · rintro ⟨x,hx,rfl⟩
        refine ⟨(hmatch x).mpr hx.1,rvUnitValues_gammaProper x,?_⟩
        rw [gammaSyntax_decode_rvUnitValues]
        exact (globalGammaPattern_semantics D _ _ (e i) x).mpr hx.2
      · rintro ⟨hz,hproper,hp⟩
        obtain ⟨x,hx⟩ := (Set.ext_iff.mp rvUnitValues_range z).mpr hproper
        subst z
        refine ⟨x,⟨(hmatch x).mp hz,?_⟩,rfl⟩
        exact (globalGammaPattern_semantics D _ _ (e i) x).mp (by rwa [gammaSyntax_decode_rvUnitValues] at hp)
    apply (integrationGammaDefinable_iff ?_).mpr
    · rw [he]
      exact hh
    · rintro z ⟨x,hx,rfl⟩ j
      exact (x j).val.property
  have hCX : ∀ i, {x | rvUnitValues x ∈ X i} = C (e i) := by
    intro i
    ext x
    exact ⟨fun ⟨y,hy,he⟩ => rvUnitValues_injective he ▸ hy,fun hx => ⟨x,hx,rfl⟩⟩
  refine ⟨Fintype.card J,X,hX,?_,?_,?_⟩
  · intro i
    rw [hCX]
    exact rvDNFPatternCell_angularCell D _ _ (e i)
  · intro i j hij
    apply Set.disjoint_left.mpr
    rintro z ⟨x,hx,rfl⟩ ⟨y,hy,he⟩
    have he' := rvUnitValues_injective he
    subst y
    exact Set.disjoint_left.mp (rvDNFPatternCells_disjoint D _ _ (e i) (e j)
      (fun he => hij (e.injective he))) hx hy
  · intro x
    rw [hmatch x,rvDNFPatternCells_cover]
    constructor
    · rintro ⟨b,hb⟩
      obtain ⟨i,rfl⟩ := e.surjective b
      exact ⟨i,x,hb,rfl⟩
    · rintro ⟨i,y,hy,he⟩
      exact ⟨e i,rvUnitValues_injective he ▸ hy⟩
end DiamondIntegral.Section3
