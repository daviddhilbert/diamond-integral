import «section 6».OrdinaryMatchingMaps

/-! One actual ordinary matching pair with all three full maps over S.
The ordinary chains retain original-base certificates for every primitive.
The finite-aperture modification is a separate construction. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ}

structure OriginalBaseOrdinarySpecial
    (A : DefSet (rawMixedSpace (M := M) n r) S)
    (B : DefSet (rawMixedSpace (M := M) n s) S) (f : Map A B) where
  codes : Set M
  contains : S ⊆ codes
  source : SpecialTransformations.Section5.DefSet (M := M) codes n r
  target : SpecialTransformations.Section5.DefSet (M := M) codes n s
  source_eq : SpecialTransformations.Section5.carrier source=A.carrier
  target_eq : SpecialTransformations.Section5.carrier target=B.carrier
  special : SpecialTransformations.Section5.SpecialBijection source target
  graphs : SpecialTransformations.Section5.GammaChainDefinable (ordinaryNamedGammaBase S) special.chain
  agrees : ∀ p : A,(special.toMap ⟨p.val,(Set.ext_iff.mp source_eq p.val).mpr p.property⟩).val=(f p).val

structure OriginalBaseOrdinaryUnaryMatching
    (A : DefSet (rawMixedSpace (M := M) 1 r) S)
    (B : DefSet (rawMixedSpace (M := M) 1 s) S) (f : Map A B) where
  sourceArity : ℕ
  targetArity : ℕ
  source : DefSet (rawMixedSpace (M := M) 1 sourceArity) S
  target : DefSet (rawMixedSpace (M := M) 1 targetArity) S
  sourceMap : Map A source
  targetMap : Map B target
  sourceSpecial : OriginalBaseOrdinarySpecial A source sourceMap
  targetSpecial : OriginalBaseOrdinarySpecial B target targetMap
  sourceBijective : Function.Bijective sourceMap
  targetBijective : Function.Bijective targetMap
  sourcePullback : IsRVPullback source.carrier
  targetPullback : IsRVPullback target.carrier
  map : Map source target
  bijective : Function.Bijective map
  commutes : ∀ p : A,map (sourceMap p)=targetMap (f p)
  forward : ∀ p q : source,rvCoordinates M p.val=rvCoordinates M q.val →
    rvCoordinates M (map p).val=rvCoordinates M (map q).val
  reverse : ∀ p q : target,rvCoordinates M p.val=rvCoordinates M q.val →
    rvCoordinates M (map.inverse bijective p).val=rvCoordinates M (map.inverse bijective q).val

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem original_base_ordinary_matching_exists
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (B₀ : VFGeneratedFieldBase S)
    (hsmall : Cardinal.mk (S : Set M) < κ)
    (hnt : ∃ x : B₀.field,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 1 r) (S : Set M))
    (B : DefSet (rawMixedSpace (M := M) 1 s) (S : Set M))
    (f : Map A B) (hf : Function.Bijective f) :
    Nonempty (OriginalBaseOrdinaryUnaryMatching A B f) := by
  obtain ⟨R,hSR,a,b,A',B',TA,TB,hTA,hTB,hA',hB',hForward,hReverse,hGraph⟩ :=
    exists_ordinary_unary_matching h00 hc hκ hs hv S B₀ hsmall hnt A B f hf
  let P := ordinaryNamedGammaBase (S : Set M)
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
    (CanonicalStructure.normalize (M := M)) _ _ (S : Set M) R _ _ (toOrdinaryMap hc f) hSR
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

end DiamondIntegral.Section6
