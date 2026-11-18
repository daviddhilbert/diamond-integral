import «section 6».UnaryRelativeMatchingMeasure
import «section 6».UnaryRelativeMatchingRegularization
import «section 6».UnaryRelativeMatchingFieldBase
import «section 6».PreparedUnaryRVMatching

/-! The measured RV bijection of completed auxiliary unary preparations.
The actual RV map, complete form graphs and radius identity are obtained
from whole prepared discs and the checked generic Jacobian transport. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r s : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S} {B : DefSet (rawMixedSpace (M := M) 1 s) S}
variable {f : Map A B}

/-- The transported form `ω ∘ T_A⁻¹` is constant on every final RV-label fibre
whenever `ω` is constant on the original label fibres. -/
theorem UnaryRelativePreparedMatching.sourceForm_extension_constant
    (H : UnaryRelativePreparedMatching (G := G) A B f) (h00 : M ⊨ Axioms.ACVF00)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hω : ∀ a b : A,a.val.2=b.val.2 → ω a=ω b) :
    ∀ p ∈ H.source.carrier,∀ q ∈ H.source.carrier,p.2=q.2 →
      gammaFormExtension (H.sourceForm h00 ω) p=gammaFormExtension (H.sourceForm h00 ω) q := by
  intro p hp q hq hTags
  rw [gammaFormExtension_at _ ⟨p,hp⟩,gammaFormExtension_at _ ⟨q,hq⟩]
  exact congrArg (fun z : DefSet.univ (rawGammaPresentation (M := M)) S => z.val)
    (H.sourceForm_constant h00 ω hω ⟨p,hp⟩ ⟨q,hq⟩ hTags)

/-- The transported form `σ ∘ T_B⁻¹` is constant on every final RV-label fibre
whenever `σ` is constant on the original label fibres. -/
theorem UnaryRelativePreparedMatching.targetForm_extension_constant
    (H : UnaryRelativePreparedMatching (G := G) A B f) (h00 : M ⊨ Axioms.ACVF00)
    (σ : Map B (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hσ : ∀ a b : B,a.val.2=b.val.2 → σ a=σ b) :
    ∀ p ∈ H.target.carrier,∀ q ∈ H.target.carrier,p.2=q.2 →
      gammaFormExtension (H.targetForm h00 σ) p=gammaFormExtension (H.targetForm h00 σ) q := by
  intro p hp q hq hTags
  rw [gammaFormExtension_at _ ⟨p,hp⟩,gammaFormExtension_at _ ⟨q,hq⟩]
  exact congrArg (fun z : DefSet.univ (rawGammaPresentation (M := M)) S => z.val)
    (H.targetForm_constant h00 σ hσ ⟨p,hp⟩ ⟨q,hq⟩ hTags)

theorem UnaryRelativePreparedMatching.rv_matching_exists
    (H : UnaryRelativePreparedMatching (G := G) A B f)
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hf : Function.Bijective f) (j : Fin H.sourceArity) (k : Fin H.targetArity)
    (hLeadA : ∀ p ∈ H.source.carrier,rv M (p.1 0)=p.2 j)
    (hLeadB : ∀ p ∈ H.target.carrier,rv M (p.1 0)=p.2 k)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (σ : Map B (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hω : ∀ a b : A,a.val.2=b.val.2 → ω a=ω b)
    (hσ : ∀ a b : B,a.val.2=b.val.2 → σ a=σ b)
    (hGeneric : ∀ a : A,AlgebraicIndependent (vfParameterField S) a.val.1 →
      ∃ J : VF M,HasMixedVFJacobianAt f a J ∧ vfValue J=(gammaMapValue ω a/gammaMapValue σ (f a)).val) :
    Nonempty (PreparedUnaryRVMatching H.source H.target H.map
      (gammaFormExtension (H.sourceForm h00 ω)) (gammaFormExtension (H.targetForm h00 σ)) j k) := by
  letI : CharZero (VF M) := vf_charZero_of_model00 h00
  obtain ⟨E,hEA,hDim,hMeasure⟩ := H.measure_exception h00 hc hκ.le hs hsmall hv hf ω σ hGeneric
  have hω' := H.sourceForm_extension_constant h00 ω hω
  have hσ' := H.targetForm_extension_constant h00 σ hσ
  apply prepared_unary_rv_matching_exists hc hκ hs h00 hsmall hv H.source H.target H.map H.bijective H.wholeFibres
    H.sourceProper H.sourceBounded H.sourcePullback H.targetProper H.targetBounded H.targetPullback j k hLeadA hLeadB
    (gammaFormExtension (H.sourceForm h00 ω)) (gammaFormExtension (H.targetForm h00 σ))
    (gammaFormExtension_graph_definable _) (gammaFormExtension_graph_definable _) hω' hσ' E hDim
  intro p hp
  obtain ⟨J,hJ,hVal⟩ := hMeasure p hp
  refine ⟨J,hJ,?_⟩
  simpa only [gammaFormExtension_at,gammaMapValue] using hVal

structure UnaryRelativeMeasuredMatching
    (A : DefSet (rawMixedSpace (M := M) 1 r) S) (B : DefSet (rawMixedSpace (M := M) 1 s) S) (f : Map A B)
    (h00 : M ⊨ Axioms.ACVF00)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (σ : Map B (DefSet.univ (rawGammaPresentation (M := M)) S)) where
  geometry : UnaryRelativePreparedMatching (G := G) A B f
  sourceIndex : Fin geometry.sourceArity
  targetIndex : Fin geometry.targetArity
  sourceLeading : ∀ p ∈ geometry.source.carrier,rv M (p.1 0)=p.2 sourceIndex
  targetLeading : ∀ p ∈ geometry.target.carrier,rv M (p.1 0)=p.2 targetIndex
  rv : PreparedUnaryRVMatching geometry.source geometry.target geometry.map
    (gammaFormExtension (geometry.sourceForm h00 ω)) (gammaFormExtension (geometry.targetForm h00 σ)) sourceIndex targetIndex
  /-- Lemma 6.38: `ω' = ω ∘ T_A⁻¹` is `rv`-contractible, i.e. constant on every
  final RV-label fibre of `A♭`. -/
  sourceContractible : ∀ p ∈ geometry.source.carrier,∀ q ∈ geometry.source.carrier,p.2=q.2 →
    gammaFormExtension (geometry.sourceForm h00 ω) p=gammaFormExtension (geometry.sourceForm h00 ω) q
  /-- Lemma 6.38: `σ' = σ ∘ T_B⁻¹` is `rv`-contractible, i.e. constant on every
  final RV-label fibre of `B♭`. -/
  targetContractible : ∀ p ∈ geometry.target.carrier,∀ q ∈ geometry.target.carrier,p.2=q.2 →
    gammaFormExtension (geometry.targetForm h00 σ) p=gammaFormExtension (geometry.targetForm h00 σ) q

theorem unary_relative_measured_prepared_matching_exists
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (B₀ : VFGeneratedFieldBase S)
    (hsmall : Cardinal.mk (S : Set M) < κ)
    (hnt : ∃ x : B₀.field,x≠0 ∧ Valued.v x.val≠1)
    (A : DefSet (rawMixedSpace (M := M) 1 r) (S : Set M))
    (B : DefSet (rawMixedSpace (M := M) 1 s) (S : Set M))
    (f : Map A B) (hf : ProperCovariantHomeomorphism f)
    (hA : ProperInvariant (S : Set M) A.carrier) (hAD : VFDoublyBounded A.carrier) (hARV : IsRVPullback A.carrier)
    (hATag : ∀ p ∈ A.carrier,∀ q ∈ A.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1)
    (hB : ProperInvariant (S : Set M) B.carrier) (hBD : VFDoublyBounded B.carrier) (hBRV : IsRVPullback B.carrier)
    (hBTag : ∀ p ∈ B.carrier,∀ q ∈ B.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1)
    (hFinite : ∀ a : Fin 1 → VF M,{u : Fin r → RVInfinity M | (a,u) ∈ A.carrier}.Finite)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) (S : Set M)))
    (σ : Map B (DefSet.univ (rawGammaPresentation (M := M)) (S : Set M)))
    (hω : ∀ a b : A,a.val.2=b.val.2 → ω a=ω b)
    (hσ : ∀ a b : B,a.val.2=b.val.2 → σ a=σ b)
    (hGeneric : ∀ a : A,AlgebraicIndependent (vfParameterField (S : Set M)) a.val.1 →
      ∃ J : VF M,HasMixedVFJacobianAt f a J ∧ vfValue J=(gammaMapValue ω a/gammaMapValue σ (f a)).val) :
    Nonempty (UnaryRelativeMeasuredMatching (G := G) A B f h00 ω σ) := by
  obtain ⟨H⟩ := unary_relative_prepared_matching_exists h00 hc hκ hs hv S B₀ hsmall hnt A B f hf
    hA hAD hARV hATag hB hBD hBRV hBTag hFinite
  let W := H.regularized h00 hc hκ hs hv
  obtain ⟨R⟩ := W.rv_matching_exists h00 hc hκ hs hsmall hv hf.bijective
    (Fin.castAdd H.sourceArity (0 : Fin 1)) (Fin.castAdd H.targetArity (0 : Fin 1))
    (H.regularized_source_leading h00 hc hκ hs hv) (H.regularized_target_leading h00 hc hκ hs hv)
    ω σ hω hσ hGeneric
  exact ⟨⟨W,_,_,H.regularized_source_leading h00 hc hκ hs hv,
    H.regularized_target_leading h00 hc hκ hs hv,R,
    W.sourceForm_extension_constant h00 ω hω,W.targetForm_extension_constant h00 σ hσ⟩⟩

end DiamondIntegral.Section6
