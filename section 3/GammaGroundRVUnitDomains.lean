import «section 3».GammaGroundFullRVCodeLogic
import «section 3».RVUnitDomains
import «section 3».FullGammaPresentations
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

theorem rawRVUnitSpace_code_proper (z : Fin n → M) (hz : z ∈ (rawRVUnitSpace (M := M) n).domain) :
    ∀ i, iRV (z i) := by
  obtain ⟨x,rfl⟩ := hz
  exact fun i => (x i).val.property

theorem rvUnitSpace_preimage_eq_image (A : Set (Fin n → (CanonicalRV.RVSort M)ˣ)) :
    (rawRVUnitSpace n).preimage A = rvUnitValues '' A := by
  ext z
  constructor
  · rintro ⟨hz,hx⟩
    exact ⟨(rawRVUnitSpace n).decode ⟨z,hz⟩,hx,rvUnitValues_decode _⟩
  · rintro ⟨x,hx,rfl⟩
    exact ⟨Set.mem_range_self x,by rwa [decode_rvUnitValues]⟩

theorem gammaGroundRVUnit_definable_iff (A : Set (Fin n → (CanonicalRV.RVSort M)ˣ)) :
    GammaGroundDefinable hc B (rawRVUnitSpace n) A ↔
      DefinableOverBase B (fun _ => .rv) (rvUnitValues '' A) := by
  rw [gammaGroundDefinable_iff_full_rv_codes (rawRVUnitSpace n) rawRVUnitSpace_code_proper,
    rvUnitSpace_preimage_eq_image]
  have hp : ∀ z ∈ rvUnitValues '' A, ∀ i, sortEval SortTag.rv (z i) := by
    rintro z ⟨x,hx,rfl⟩ i
    exact (x i).val.property
  exact (integrationGammaDefinable_iff hp).symm

def gammaGroundRVUnitSetOfBase (A : Set (Fin n → M))
    (hA : DefinableOverBase B (fun _ => .rv) A) : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n) := by
  refine ⟨{x | rvUnitValues x ∈ A},?_⟩
  apply (gammaGroundDefinable_iff_full_rv_codes _ rawRVUnitSpace_code_proper _).mpr
  have hNZ := FullRawDefinable.forall_finite (fun i : Fin n => fullRaw_nonzero (integrationGammaBase B) i)
  have hh := hNZ.and (integrationGammaDefinable hA)
  apply FullBaseAtomicity.OverBase.congr hh
  intro z
  change ((∀ i, NonzeroRV (z i)) ∧ z ∈ A) ↔
    ∃ hz : z ∈ (rawRVUnitSpace n).domain, rvUnitValues ((rawRVUnitSpace n).decode ⟨z,hz⟩) ∈ A
  constructor
  · rintro ⟨hz,hA⟩
    have hc : z ∈ (rawRVUnitSpace (M := M) n).domain := (Set.ext_iff.mp rvUnitValues_range z).mpr hz
    exact ⟨hc,by rwa [rvUnitValues_decode]⟩
  · rintro ⟨hz,hA⟩
    exact ⟨(Set.ext_iff.mp rvUnitValues_range z).mp hz,by rwa [rvUnitValues_decode] at hA⟩

theorem gammaPower_code_proper (hc : CanonicalStructure.IsCanonical (M := M))
    (z : Fin n × Fin 1 → M) (hz : z ∈ ((volumeGammaSpace hc).power (Fin n)).domain) :
    ∀ i, iRV (z i) := by
  rintro ⟨i,j⟩
  have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
  subst j
  exact (hz i).1

/-- A full Gamma predicate over the original mixed base gives a genuine
Gamma-ground definable set, without naming a code representative. -/
theorem gammaGroundGammaPower_predicate_definable
    (P : (Fin n → Values.Gamma (M := M)) → Prop)
    (hP : FullGammaSyntax.Definable (integrationGammaBase B) P) :
    GammaGroundDefinable hc B ((volumeGammaSpace hc).power (Fin n)) {γ | P γ} := by
  apply (gammaGroundDefinable_iff_full_rv_codes _ (gammaPower_code_proper hc) _).mpr
  have hh := FullRawDefinable.reindex hP (fun i : Fin n => (i,(0 : Fin 1)))
  apply FullBaseAtomicity.OverBase.congr hh
  intro z
  change Fin n × Fin 1 → M at z
  change (GammaSyntax.Proper (fun i => z (i,0)) ∧ P (GammaSyntax.decode (fun i => z (i,0)))) ↔
    ∃ hz : z ∈ ((volumeGammaSpace hc).power (Fin n)).domain,
      P (((volumeGammaSpace hc).power (Fin n)).decode ⟨z,hz⟩)
  have he (hz : z ∈ ((volumeGammaSpace hc).power (Fin n)).domain) :
      ((volumeGammaSpace hc).power (Fin n)).decode ⟨z,hz⟩ = GammaSyntax.decode (fun i => z (i,0)) := by
    funext i
    exact (codeValue_raw ⟨⟨z (i,0),(hz i).1⟩,(hz i).2⟩).symm
  exact ⟨fun ⟨hz,hp⟩ => ⟨hz,(he hz).symm ▸ hp⟩,fun ⟨hz,hp⟩ => ⟨hz,(he hz) ▸ hp⟩⟩
end DiamondIntegral.Section3
