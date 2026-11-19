import «section 6».OrdinaryUnaryMatching
import «section 6».OriginalBaseOrdinaryMatching
import «section 6».UnaryRelativeRVFamilyMeasuredMatching
import «section 6».BoundedVariableUnaryMatching
import «section 6».DiamondSimultaneous
import Integration7.UnaryCompatiblePreparationWithoutField

/-! Lemma 6.38 over a set-based base (for base change in Section 7).

Section 6 states Lemma 6.38 over a substructure `S` with a VF field base. Its
proof uses that base only through the support data `V ⊆ S ⊆ acl(V)` (`V` a set
of VF names whose algebraic closure field has a nontrivial valuation), except
in the cited ordinary matching, which used the field base of `S`. Upstream's
`lemma_5_2_gamma_presented_without_field` (integration-in-ACVF, Section 7)
removes that use. The copies below repeat Section 6's proofs with the support
data in place of the field base; the statements are otherwise unchanged. A set
such as `S ∪ range a` (adjoined VF parameters) then serves as the base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section7.SetBaseMatching
open DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {r s : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_ordinary_unary_matching_of_support
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S V : Set M) (hV : ∀ x ∈ V,iVF x) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt' : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (hsmall : Cardinal.mk S < κ)
    (A : DefSet (rawMixedSpace (M := M) 1 r) S)
    (B : DefSet (rawMixedSpace (M := M) 1 s) S)
    (f : Map A B) (hf : Function.Bijective f) :
    ∃ R : Set M, ∃ hSR : S ⊆ R,
      ∃ a b : ℕ, ∃ A' : SpecialTransformations.Section5.DefSet (M := M) R 1 a,
      ∃ B' : SpecialTransformations.Section5.DefSet (M := M) R 1 b,
      ∃ TA : SpecialTransformations.Section5.SpecialBijection
        (SpecialTransformations.Section5.extendBase (toOrdinarySet hc A) hSR) A',
      ∃ TB : SpecialTransformations.Section5.SpecialBijection
        (SpecialTransformations.Section5.extendBase (toOrdinarySet hc B) hSR) B',
        SpecialTransformations.Section5.GammaChainDefinable (ordinaryNamedGammaBase S) TA.chain ∧
        SpecialTransformations.Section5.GammaChainDefinable (ordinaryNamedGammaBase S) TB.chain ∧
        SpecialTransformations.Section5.IsRVPullback (SpecialTransformations.Section5.carrier A') ∧
        SpecialTransformations.Section5.IsRVPullback (SpecialTransformations.Section5.carrier B') ∧
        let fR := @SpecialTransformations.DefinableGeometry.Map.extend LRV M
          (CanonicalStructure.normalize (M := M)) _ _ S R _ _ (toOrdinaryMap hc f) hSR
        SpecialTransformations.Section5.Contractible (IntegrationInACVF.Section5.unaryConjugate TA TB fR) ∧
        SpecialTransformations.Section5.Contractible
          (SpecialTransformations.Section5.Map.inverse (IntegrationInACVF.Section5.unaryConjugate TA TB fR)
            (IntegrationInACVF.Section5.unaryConjugate_bijective TA TB fR hf)) ∧
        SpecialTransformations.Section5.GammaGraphDefinable (ordinaryNamedGammaBase S)
          (SpecialTransformations.Section5.pointMapGraph (IntegrationInACVF.Section5.unaryConjugate TA TB fR)) := by
  obtain ⟨c,hc0,hcDef,hcVal⟩ := exists_named_vf_above_radius Valued.v hv hc h00
    V S hV hVS hSV hnt' 1 le_rfl (gamma_one_named hc)
  let δ := finiteValue c hc0
  have hδ : δ ∈ (ordinaryNamedGammaBase S).gamma := finiteValue_named c hc0 hcDef
  have hδ1 : 1 < δ := hcVal
  let P := ordinaryNamedGammaBase S
  have hA := (SpecialTransformations.Section5.gammaLogicInput P).real_set _
    (SpecialTransformations.Section5.setDefinable (toOrdinarySet hc A))
  have hB := (SpecialTransformations.Section5.gammaLogicInput P).real_set _
    (SpecialTransformations.Section5.setDefinable (toOrdinarySet hc B))
  have hF := (SpecialTransformations.Section5.gammaLogicInput P).real_map_graph (toOrdinaryMap hc f)
  obtain ⟨R,hSR,a,b,A',B',TA,TB,hTA,hTB,hA',hB',hForward,hReverse,hGraph,hKeys⟩ :=
    IntegrationInACVF.Section7.lemma_5_2_gamma_presented_without_field (P := P) hκ hs hsmall h00 δ hδ hδ1
      (fun _ h => h) (toOrdinaryMap hc f) hf hA hB hF
  exact ⟨R,hSR,a,b,A',B',TA,TB,hTA,hTB,hA',hB',hForward,hReverse,hGraph⟩


theorem original_base_ordinary_matching_exists_of_support
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S V : Set M) (hV : ∀ x ∈ V,iVF x) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt' : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (hsmall : Cardinal.mk S < κ)
    (A : DefSet (rawMixedSpace (M := M) 1 r) S)
    (B : DefSet (rawMixedSpace (M := M) 1 s) S)
    (f : Map A B) (hf : Function.Bijective f) :
    Nonempty (OriginalBaseOrdinaryUnaryMatching A B f) := by
  obtain ⟨R,hSR,a,b,A',B',TA,TB,hTA,hTB,hA',hB',hForward,hReverse,hGraph⟩ :=
    exists_ordinary_unary_matching_of_support h00 hc hκ hs hv S V hV hVS hSV hnt' hsmall A B f hf
  let P := ordinaryNamedGammaBase S
  let L := SpecialTransformations.Section5.gammaLogicInput P
  have hAΓ := SpecialTransformations.Section5.GammaChainDefinable.target P TA.chain hTA
  have hBΓ := SpecialTransformations.Section5.GammaChainDefinable.target P TB.chain hTB
  let A₁ := originalBaseOrdinarySet hc A' hAΓ
  let B₁ := originalBaseOrdinarySet hc B' hBΓ
  let α : Map A A₁ := ⟨TA.toMap,ordinary_named_gamma_graph_definable hc _
    (SpecialTransformations.Section5.GammaChainDefinable.graph L TA.chain hTA)⟩
  let β : Map B B₁ := ⟨TB.toMap,ordinary_named_gamma_graph_definable hc _
    (SpecialTransformations.Section5.GammaChainDefinable.graph L TB.chain hTB)⟩
  let fR := @SpecialTransformations.DefinableGeometry.Map.extend LRV M
    (CanonicalStructure.normalize (M := M)) _ _ S R _ _ (toOrdinaryMap hc f) hSR
  let g := IntegrationInACVF.Section5.unaryConjugate TA TB fR
  let g₁ : Map A₁ B₁ := originalBaseOrdinaryMap hc hAΓ hBΓ g hGraph
  have hg : Function.Bijective g₁ := IntegrationInACVF.Section5.unaryConjugate_bijective TA TB fR hf
  refine ⟨{
    sourceArity := a
    targetArity := b
    source := A₁
    target := B₁
    sourceMap := α
    targetMap := β
    sourceSpecial := ⟨R,hSR,_,A',rfl,rfl,TA,hTA,fun _ => rfl⟩
    targetSpecial := ⟨R,hSR,_,B',rfl,rfl,TB,hTB,fun _ => rfl⟩
    sourceBijective := TA.bijective
    targetBijective := TB.bijective
    sourcePullback := (ordinary_pullback_iff _).mp hA'
    targetPullback := (ordinary_pullback_iff _).mp hB'
    map := g₁
    bijective := hg
    commutes := ?_
    forward := originalBaseOrdinaryMap_contractible hc hAΓ hBΓ g hGraph hForward
    reverse := ?_ }⟩
  · intro p
    apply Subtype.ext
    change (TB.toMap (fR (TA.inverseMap (TA.toMap p)))).val=(TB.toMap (fR p)).val
    rw [TA.inverse_apply]
  · intro p q hpq
    have h := hReverse p q ((ordinary_sameRV_iff _ _).mpr (Prod.mk.inj hpq))
    have h' := (ordinary_sameRV_iff _ _).mp h
    exact Prod.ext h'.1 h'.2


theorem unary_relative_rv_family_prepared_matching_exists_of_support
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S V : Set M) (hV : ∀ x ∈ V,iVF x) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt' : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (A : DefSet (rawMixedSpace (M := M) 1 r) S)
    (B : DefSet (rawMixedSpace (M := M) 1 s) S)
    (f : Map A B) (hf : ProperCovariantHomeomorphism f)
    (hA : ProperInvariant S A.carrier) (hAD : VFDoublyBounded A.carrier) (hARV : IsRVPullback A.carrier)
    (hATag : ∀ p ∈ A.carrier,∀ q ∈ A.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1)
    (hB : ProperInvariant S B.carrier) (hBD : VFDoublyBounded B.carrier) (hBRV : IsRVPullback B.carrier)
    (hBTag : ∀ p ∈ B.carrier,∀ q ∈ B.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1)
    :
    Nonempty (UnaryRelativePreparedMatching (G := G) A B f) := by
  obtain ⟨F⟩ := original_base_ordinary_matching_exists_of_support h00 hc hκ hs hv S V hV hVS hSV hnt' hsmall A B f hf.bijective
  exact unary_relative_rv_family_matching_of_ordinary h00 hc linear hκ hs hv V hsmall hΓ
    hV hVS hSV hnt' f hf hA hAD hARV hATag hB hBD hBRV hBTag F

theorem unary_relative_measured_rv_family_prepared_matching_exists_of_support
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S V : Set M) (hV : ∀ x ∈ V,iVF x) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt' : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (A : DefSet (rawMixedSpace (M := M) 1 r) S)
    (B : DefSet (rawMixedSpace (M := M) 1 s) S)
    (f : Map A B) (hf : ProperCovariantHomeomorphism f)
    (hA : ProperInvariant S A.carrier) (hAD : VFDoublyBounded A.carrier) (hARV : IsRVPullback A.carrier)
    (hATag : ∀ p ∈ A.carrier,∀ q ∈ A.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1)
    (hB : ProperInvariant S B.carrier) (hBD : VFDoublyBounded B.carrier) (hBRV : IsRVPullback B.carrier)
    (hBTag : ∀ p ∈ B.carrier,∀ q ∈ B.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (σ : Map B (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hω : ∀ a b : A,a.val.2=b.val.2 → ω a=ω b)
    (hσ : ∀ a b : B,a.val.2=b.val.2 → σ a=σ b)
    (hGeneric : ∀ a : A,AlgebraicIndependent (vfParameterField S) a.val.1 →
      ∃ J : VF M,HasMixedVFJacobianAt f a J ∧ vfValue J=(gammaMapValue ω a/gammaMapValue σ (f a)).val) :
    Nonempty (UnaryRelativeMeasuredMatching (G := G) A B f h00 ω σ) := by
  obtain ⟨H⟩ := unary_relative_rv_family_prepared_matching_exists_of_support h00 hc linear hκ hs hv S V hV hVS hSV hnt' hsmall hΓ A B f hf
    hA hAD hARV hATag hB hBD hBRV hBTag
  let W := H.regularized h00 hc hκ hs hv
  obtain ⟨R⟩ := W.rv_matching_exists h00 hc hκ hs hsmall hv hf.bijective
    (Fin.castAdd H.sourceArity (0 : Fin 1)) (Fin.castAdd H.targetArity (0 : Fin 1))
    (H.regularized_source_leading h00 hc hκ hs hv) (H.regularized_target_leading h00 hc hκ hs hv)
    ω σ hω hσ hGeneric
  exact ⟨⟨W,_,_,H.regularized_source_leading h00 hc hκ hs hv,
    H.regularized_target_leading h00 hc hκ hs hv,R,
    W.sourceForm_extension_constant h00 ω hω,W.targetForm_extension_constant h00 σ hσ⟩⟩

theorem unary_relative_measured_rv_family_matching_exists_of_support
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S V : Set M) (hV : ∀ x ∈ V,iVF x) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt' : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (A : DefSet (rawMixedSpace (M := M) 1 r) S)
    (B : DefSet (rawMixedSpace (M := M) 1 s) S)
    (f : Map A B) (hf : ProperCovariantHomeomorphism f)
    (hA : ProperInvariant S A.carrier) (hB : ProperInvariant S B.carrier)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (σ : Map B (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hωLevels : ∀ u γ,IsOpen {a : Fin 1 → VF M | (a,u) ∈ A.carrier ∧ gammaFormExtension ω (a,u)=γ})
    (hσLevels : ∀ u γ,IsOpen {a : Fin 1 → VF M | (a,u) ∈ B.carrier ∧ gammaFormExtension σ (a,u)=γ})
    (hGeneric : ∀ a : A,AlgebraicIndependent (vfParameterField S) a.val.1 →
      ∃ J : VF M,HasMixedVFJacobianAt f a J ∧ vfValue J=(gammaMapValue ω a/gammaMapValue σ (f a)).val) :
    Nonempty (UnaryRelativeMeasuredMatching (G := G) A B f h00 ω σ) := by
  letI : CharZero (VF M) := vf_charZero_of_model00 h00
  let C : Fin 0 → DefSet (rawMixedSpace (M := M) 1 r) S := Fin.elim0
  let D : Fin 0 → DefSet (rawMixedSpace (M := M) 1 s) S := Fin.elim0
  obtain ⟨P⟩ := measured_proper_preparation h00 hc linear hκ hs hv V hsmall hΓ
    hV hVS hSV hnt' A hA C (fun i => i.elim0) (fun i => i.elim0) ω hωLevels
  obtain ⟨Q⟩ := measured_proper_preparation h00 hc linear hκ hs hv V hsmall hΓ
    hV hVS hSV hnt' B hB D (fun i => i.elim0) (fun i => i.elim0) σ hσLevels
  have hPHome := P.special.properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ
  have hQHome := Q.special.properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ
  let inv := P.map.inverse (P.special.bijective h00)
  let g := Q.map.comp (f.comp inv)
  have hInvHome : ProperCovariantHomeomorphism inv :=
    inverse_properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ P.map hPHome
  have hg : ProperCovariantHomeomorphism g :=
    lemma_6_9 h00 hc linear hκ hs hv hsmall hΓ
      (lemma_6_9 h00 hc linear hκ hs hv hsmall hΓ hInvHome hf) hQHome
  have hPConst (p q : P.target) (hTags : p.val.2=q.val.2) : P.form p=P.form q := by
    apply Subtype.ext
    have h := P.constant p.val p.property q.val q.property hTags
    simpa only [gammaFormExtension_at] using h
  have hQConst (p q : Q.target) (hTags : p.val.2=q.val.2) : Q.form p=Q.form q := by
    apply Subtype.ext
    have h := Q.constant p.val p.property q.val q.property hTags
    simpa only [gammaFormExtension_at] using h
  have hGCommutes (p : A) : g (P.map p)=Q.map (f p) := by
    change Q.map (f (P.map.inverse _ (P.map p)))=Q.map (f p)
    rw [Map.inverse_apply]
  have hGGeneric (p : P.target) (hp : AlgebraicIndependent (vfParameterField S) p.val.1) :
      ∃ J : VF M,HasMixedVFJacobianAt g p J ∧
        vfValue J=(gammaMapValue P.form p/gammaMapValue Q.form (g p)).val := by
    let a := inv p
    have hInvInj : Function.Injective inv := by
      intro x y he
      have h := congrArg P.map he
      simpa only [inv,Map.apply_inverse] using h
    have ha := independent_map_of_finiteFibres hc inv (Map.finiteFibres_of_injective hInvInj) p hp
    obtain ⟨J,hJ,hVal⟩ := hGeneric a ha
    have hGJ := unary_unit_preparation_conjugate_jacobian h00 hc hκ.le hs hsmall hv
      P.map Q.map (.original P.special) (.original Q.special) f hf.bijective p hp J hJ
    have hPAt : P.form p=ω a := by
      have hp' : P.map a=p := Map.apply_inverse P.map (P.special.bijective h00) p
      rw [← hp']
      exact Subtype.ext (P.transport a)
    have hQAt : Q.form (g p)=σ (f a) := Subtype.ext (Q.transport (f a))
    have hRatio : gammaMapValue P.form p/gammaMapValue Q.form (g p)=
        gammaMapValue ω a/gammaMapValue σ (f a) := by
      unfold gammaMapValue
      rw [hPAt,hQAt]
    refine ⟨J,hGJ,?_⟩
    rw [hRatio]
    exact hVal
  obtain ⟨R⟩ := unary_relative_measured_rv_family_prepared_matching_exists_of_support h00 hc linear hκ hs hv S V hV hVS hSV hnt' hsmall hΓ
    P.target Q.target g hg P.proper P.doublyBounded P.prepared P.tagged
    Q.proper Q.doublyBounded Q.prepared Q.tagged P.form Q.form hPConst hQConst hGGeneric
  exact ⟨R.precompose P.map Q.map (.original P.special) (.original Q.special) hGCommutes
    h00 ω σ P.form Q.form (fun p => Subtype.ext (P.transport p)) (fun p => Subtype.ext (Q.transport p))⟩


theorem lemma_6_38_bounded_variable_apertures_of_support
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S V : Set M) (hV : ∀ x ∈ V,iVF x) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt' : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (A : DefSet (rawMixedSpace (M := M) 1 r) S)
    (B : DefSet (rawMixedSpace (M := M) 1 s) S)
    (f : Map A B) (hf : ProperCovariantHomeomorphism f)
    (hA : ProperInvariant S A.carrier) (hB : ProperInvariant S B.carrier)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (σ : Map B (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hωLevels : ∀ u γ,IsOpen {a : Fin 1 → VF M | (a,u) ∈ A.carrier ∧ gammaFormExtension ω (a,u)=γ})
    (hσLevels : ∀ u γ,IsOpen {a : Fin 1 → VF M | (a,u) ∈ B.carrier ∧ gammaFormExtension σ (a,u)=γ})
    (hGeneric : ∀ a : A,AlgebraicIndependent (vfParameterField S) a.val.1 →
      ∃ J : VF M,HasMixedVFJacobianAt f a J ∧ vfValue J=(gammaMapValue ω a/gammaMapValue σ (f a)).val) :
    ∃ H : UnaryRelativeMeasuredMatching (G := G) A B f h00 ω σ,
      RelativeApertureChain (G := G) A H.geometry.source H.geometry.sourceMap ∧
      RelativeApertureChain (G := G) B H.geometry.target H.geometry.targetMap := by
  obtain ⟨H⟩ := unary_relative_measured_rv_family_matching_exists_of_support h00 hc linear hκ hs hv S V hV hVS hSV hnt' hsmall hΓ
    A B f hf hA hB ω σ hωLevels hσLevels hGeneric
  exact ⟨H,H.geometry.sourceChain.toRelativeChain hc h00 linear hκ.le hs hsmall hΓ,
    H.geometry.targetChain.toRelativeChain hc h00 linear hκ.le hs hsmall hΓ⟩

/-- Lemma 6.38 (`simul:special:dim:1`) with its final clauses. Besides the
bounded variable-aperture chains `T_A`, `T_B` and the measured RV matching,
the transported forms `ω' = ω ∘ T_A⁻¹` and `σ' = σ ∘ T_B⁻¹` are
`rv`-contractible, and the induced map `f♭_↓` is a morphism of `μRV^db[1]`
from `(rv(A♭), ω')_1` to `(rv(B♭), σ')_1`: both contracted objects are doubly
bounded measured RV objects whose finite-to-one volume map is the projection to
the leading label (Notation `0coor`), and `f♭_↓` is a measured RV isomorphism
commuting with the label quotients. The finite RV fibres of `A` (an object of
`VF[1]`, Definition `defn:VF:cat`) give the finite RV fibres of `A♭`, `B♭` by
Lemma `RV:fiber:dim:same`. -/
theorem lemma_6_38_bounded_variable_apertures_contractible_of_support
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S V : Set M) (hV : ∀ x ∈ V,iVF x) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt' : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (A : DefSet (rawMixedSpace (M := M) 1 r) S)
    (B : DefSet (rawMixedSpace (M := M) 1 s) S)
    (f : Map A B) (hf : ProperCovariantHomeomorphism f)
    (hA : ProperInvariant S A.carrier) (hB : ProperInvariant S B.carrier)
    (hFinite : ∀ a : Fin 1 → VF M,{u : Fin r → RVInfinity M | (a,u) ∈ A.carrier}.Finite)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (σ : Map B (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hωLevels : ∀ u γ,IsOpen {a : Fin 1 → VF M | (a,u) ∈ A.carrier ∧ gammaFormExtension ω (a,u)=γ})
    (hσLevels : ∀ u γ,IsOpen {a : Fin 1 → VF M | (a,u) ∈ B.carrier ∧ gammaFormExtension σ (a,u)=γ})
    (hGeneric : ∀ a : A,AlgebraicIndependent (vfParameterField S) a.val.1 →
      ∃ J : VF M,HasMixedVFJacobianAt f a J ∧ vfValue J=(gammaMapValue ω a/gammaMapValue σ (f a)).val) :
    ∃ H : UnaryRelativeMeasuredMatching (G := G) A B f h00 ω σ,
      RelativeApertureChain (G := G) A H.geometry.source H.geometry.sourceMap ∧
      RelativeApertureChain (G := G) B H.geometry.target H.geometry.targetMap ∧
      (∀ p ∈ H.geometry.source.carrier,∀ q ∈ H.geometry.source.carrier,p.2=q.2 →
        gammaFormExtension (H.geometry.sourceForm h00 ω) p=gammaFormExtension (H.geometry.sourceForm h00 ω) q) ∧
      (∀ p ∈ H.geometry.target.carrier,∀ q ∈ H.geometry.target.carrier,p.2=q.2 →
        gammaFormExtension (H.geometry.targetForm h00 σ) p=gammaFormExtension (H.geometry.targetForm h00 σ) q) ∧
      ∃ (hA' : ∀ a : Fin 1 → VF M,{u : Fin H.geometry.sourceArity → RVInfinity M |
            (a,u) ∈ H.geometry.source.carrier}.Finite)
        (hB' : ∀ b : Fin 1 → VF M,{v : Fin H.geometry.targetArity → RVInfinity M |
            (b,v) ∈ H.geometry.target.carrier}.Finite),
        (H.sourceRV hA').doublyBounded ∧ (H.targetRV hB').doublyBounded ∧
        (∀ u,(H.sourceRV hA').object.value u=fun _ => u.val H.sourceIndex) ∧
        (∀ v,(H.targetRV hB').object.value v=fun _ => v.val H.targetIndex) ∧
        ∃ e : MeasuredRVIso (H.sourceRV hA') (H.targetRV hB'),
          ∀ p : H.geometry.source,
            e.iso.hom.map (pureRVTagQuotient H.geometry.source p)=
              pureRVTagQuotient H.geometry.target (H.geometry.map p) := by
  obtain ⟨H,hSource,hTarget⟩ := lemma_6_38_bounded_variable_apertures_of_support (G := G) h00 hc linear hκ hs hv S V hV hVS hSV hnt'
    hsmall hΓ A B f hf hA hB ω σ hωLevels hσLevels hGeneric
  have hA' := finite_rv_fibers_of_bijective hc h00 hκ.le hs hsmall H.geometry.sourceMap
    (H.geometry.sourceChain.bijective h00) hFinite
  have hB' := finite_rv_fibers_of_bijective hc h00 hκ.le hs hsmall H.geometry.targetMap
    (H.geometry.targetChain.bijective h00)
    (finite_rv_fibers_of_bijective hc h00 hκ.le hs hsmall f hf.bijective hFinite)
  exact ⟨H,hSource,hTarget,H.sourceContractible,H.targetContractible,hA',hB',
    H.sourceRV_doublyBounded hA',H.targetRV_doublyBounded hB',H.sourceRV_value hA',H.targetRV_value hB',
    H.measuredRVIso hA' hB',H.measuredRVIso_map hA' hB'⟩


section Diamond
open DiamondIntegral.Section6.DiamondCategory DiamondIntegral.Section6.DiamondGroupoid
open DiamondIntegral.Section6.DiamondSimultaneous

theorem lemma_6_38_diamond_contractible_of_support (h00 : M ⊨ Axioms.ACVF00)
    (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S V : Set M) (hV : ∀ x ∈ V,iVF x) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt' : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S, ∅⟩ : ParameterBase M))
    {A B : VFObject (M := M) S 1} (F : Morphism G A B) :
    ∃ H : UnaryRelativeMeasuredMatching (G := G) A.carrier B.carrier F.map h00 A.form B.form,
      RelativeApertureChain (G := G) A.carrier H.geometry.source H.geometry.sourceMap ∧
      RelativeApertureChain (G := G) B.carrier H.geometry.target H.geometry.targetMap ∧
      (∀ p ∈ H.geometry.source.carrier, ∀ q ∈ H.geometry.source.carrier, p.2 = q.2 →
        gammaFormExtension (H.geometry.sourceForm h00 A.form) p =
          gammaFormExtension (H.geometry.sourceForm h00 A.form) q) ∧
      (∀ p ∈ H.geometry.target.carrier, ∀ q ∈ H.geometry.target.carrier, p.2 = q.2 →
        gammaFormExtension (H.geometry.targetForm h00 B.form) p =
          gammaFormExtension (H.geometry.targetForm h00 B.form) q) ∧
      ∃ (hA' : ∀ a : Fin 1 → VF M, {u : Fin H.geometry.sourceArity → RVInfinity M |
            (a, u) ∈ H.geometry.source.carrier}.Finite)
        (hB' : ∀ b : Fin 1 → VF M, {v : Fin H.geometry.targetArity → RVInfinity M |
            (b, v) ∈ H.geometry.target.carrier}.Finite),
        (H.sourceRV hA').doublyBounded ∧ (H.targetRV hB').doublyBounded ∧
        (∀ u, (H.sourceRV hA').object.value u = fun _ => u.val H.sourceIndex) ∧
        (∀ v, (H.targetRV hB').object.value v = fun _ => v.val H.targetIndex) ∧
        ∃ e : MeasuredRVIso (H.sourceRV hA') (H.targetRV hB'),
          ∀ p : H.geometry.source,
            e.iso.hom.map (pureRVTagQuotient H.geometry.source p) =
              pureRVTagQuotient H.geometry.target (H.geometry.map p) :=
  lemma_6_38_bounded_variable_apertures_contractible_of_support h00 hc linear hκ hs hv S V hV hVS hSV hnt' hsmall hΓ
    A.carrier B.carrier F.map (factor_homeo h00 hc linear hκ hs hv hsmall hΓ F.factor A.proper).1
    A.proper B.proper A.finiteRV A.form B.form (form_levels_open hv A) (form_levels_open hv B)
    (fun a ha => by
      obtain ⟨L, ⟨Fc, hFc, hL⟩, hdet⟩ := Morphism.generic hc F a ha
      exact ⟨_, ⟨Fc, hFc, hL.hasJacobianAt⟩, hdet⟩)

end Diamond

end DiamondIntegral.Section7.SetBaseMatching
