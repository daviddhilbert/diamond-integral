import «section 6».UnaryRelativePreparedMatching
import «section 6».UnaryPrescribedCoreRealization
import «section 6».SeparatedUnaryCorePlans
import «section 6».FiniteMatchingExceptions

/-! Whole prepared unary matching from an actual ordinary matching.
All paired cores, named finite-word bounds, variable endpoints and the
finite first-zero executions are constructed. Finite RV fibres are
required on the original degree-one source, not on intermediate sets. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r s : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S} {B : DefSet (rawMixedSpace (M := M) 1 s) S}

theorem unary_relative_matching_of_ordinary
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x≠0 ∧ Valued.v x.val≠1)
    (f : Map A B) (hf : ProperCovariantHomeomorphism f)
    (hA : ProperInvariant S A.carrier) (hAD : VFDoublyBounded A.carrier) (hARV : IsRVPullback A.carrier)
    (hATag : ∀ p ∈ A.carrier,∀ q ∈ A.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1)
    (hB : ProperInvariant S B.carrier) (hBD : VFDoublyBounded B.carrier) (hBRV : IsRVPullback B.carrier)
    (hBTag : ∀ p ∈ B.carrier,∀ q ∈ B.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1)
    (hFinite : ∀ a : Fin 1 → VF M,{u : Fin r → RVInfinity M | (a,u) ∈ A.carrier}.Finite)
    (F : OriginalBaseOrdinaryUnaryMatching A B f) :
    Nonempty (UnaryRelativePreparedMatching (G := G) A B f) := by
  let E := F.sourceSpecial.exceptions hc
  let hEA := F.sourceSpecial.exceptions_subset hc
  let E' := matchedCenterImage f E hEA
  let C := matchedCenterMap f E hEA
  have hC : Function.Bijective C := matchedCenterMap_bijective f E hEA hf.bijective.injective
  have hE : E.carrier.Finite := by
    have h := F.exception_domain_finite hc hκ.le hs hsmall hf.bijective hFinite
    rwa [F.paired_exception_domain_eq hc] at h
  letI : Fintype E := hE.fintype
  have hE' : E'.carrier.Finite := Set.finite_range _
  let hSrc : E.carrier ⊆ SpecialTransformations.Section5.carrier F.sourceSpecial.source :=
    fun p hp => (Set.ext_iff.mp F.sourceSpecial.source_eq p).mpr (hEA hp)
  let hTgt : E'.carrier ⊆ SpecialTransformations.Section5.carrier F.targetSpecial.source :=
    fun p hp => (Set.ext_iff.mp F.targetSpecial.source_eq p).mpr (matchedCenterImage_subset f E hEA hp)
  obtain ⟨α,hα,hα1,hαBound⟩ := ordinaryChainPointRadius_uniform_named_bound hc h00 hκ.le hs hsmall hv
    V hV hVS hSV hnt F.sourceSpecial.special.chain F.sourceSpecial.graphs E hSrc (hE.image Prod.fst)
  obtain ⟨β,hβ,hβ1,hβBound⟩ := ordinaryChainPointRadius_uniform_named_bound hc h00 hκ.le hs hsmall hv
    V hV hVS hSV hnt F.targetSpecial.special.chain F.targetSpecial.graphs E' hTgt (hE'.image Prod.fst)
  obtain ⟨D⟩ := exists_separated_unary_offset_cores h00 hc hκ.le hs hsmall hv V hV hVS hSV hnt
    f hf hARV hAD E hEA hE α β hα hβ
  have hSource (p : E) : vfValue (p.val.1 0)<α.val :=
    ordinary_chain_value_lt_pointRadius_bound F.sourceSpecial.special.chain ⟨p.val,hSrc p.property⟩ α
      (hαBound p) (hAD.nonzero (hEA p.property) 0)
  have hTarget (p : E) : vfValue ((f ⟨p.val,hEA p.property⟩).val.1 0)<β.val :=
    ordinary_chain_value_lt_pointRadius_bound F.targetSpecial.special.chain ⟨(C p).val,hTgt (C p).property⟩ β
      (hβBound (C p)) (hBD.nonzero (f ⟨p.val,hEA p.property⟩).property 0)
  let K := D.sourcePlan hE hSource
  let L := D.targetPlan hE hTarget hf.bijective.injective
  have hCoverA (a : A) : (F.sourceMap a).val.1 0=(0 : VF M) ↔ a.val ∈ K.centres.carrier :=
    (F.sourceSpecial.exceptions_iff_prepared_zero hc a).symm
  have hBoundA (p : K.centres) : ordinaryChainPointRadius F.sourceSpecial.special.chain
      ⟨p.val,(Set.ext_iff.mp F.sourceSpecial.source_eq p.val).mpr (K.subset p.property)⟩<K.radius p :=
    (hαBound p).trans (show α<finiteValue ((D.sourceOffset p).val 0) (D.sourceNonzero p) from D.sourceFloor p)
  have hImage (b : B) : b.val ∈ E'.carrier ↔ b.val ∈ (F.targetSpecial.exceptions hc).carrier := by
    constructor
    · rintro ⟨p,hpb⟩
      have he : f ⟨p.val,hEA p.property⟩=b := Subtype.ext hpb
      have hp := (F.exceptions_paired hc ⟨p.val,hEA p.property⟩).mp p.property
      rwa [he] at hp
    · intro hb
      let a := f.inverse hf.bijective b
      have ha : a.val ∈ E.carrier :=
        (F.exceptions_paired hc a).mpr (by simpa only [a,Map.apply_inverse] using hb)
      refine ⟨⟨a.val,ha⟩,?_⟩
      have h := congrArg (fun q : B => q.val) (Map.apply_inverse f hf.bijective b)
      exact h
  have hCoverB (b : B) : (F.targetMap b).val.1 0=(0 : VF M) ↔ b.val ∈ L.centres.carrier :=
    (F.targetSpecial.exceptions_iff_prepared_zero hc b).symm.trans (hImage b).symm
  have hBoundB (p : L.centres) : ordinaryChainPointRadius F.targetSpecial.special.chain
      ⟨p.val,(Set.ext_iff.mp F.targetSpecial.source_eq p.val).mpr (L.subset p.property)⟩<L.radius p := by
    obtain ⟨q,rfl⟩ := hC.surjective p
    change ordinaryChainPointRadius F.targetSpecial.special.chain
      ⟨(C q).val,hTgt (C q).property⟩<finiteValue
        ((matchedTargetOffsetMap f E hEA hf.bijective.injective D.targetOffset (C q)).val 0) _
    simpa only [C,matchedTargetOffsetMap_at] using (hβBound (C q)).trans
      (show β<finiteValue ((D.targetOffset q).val 0) (D.targetNonzero q) from D.targetFloor q)
  obtain ⟨Z,hZ⟩ := exists_unary_prescribed_core_realization h00 hc hκ hs hv hsmall
    F.sourceSpecial K hA hAD hARV hATag hCoverA hBoundA
  obtain ⟨Y,hY⟩ := exists_unary_prescribed_core_realization h00 hc hκ hs hv hsmall
    F.targetSpecial L hB hBD hBRV hBTag hCoverB hBoundB
  have hOrdinary (a b : A) :
      SpecialTransformations.Section5.SameRV (Z.ordinaryMap a).val (Z.ordinaryMap b).val ↔
        SpecialTransformations.Section5.SameRV (Y.ordinaryMap (f a)).val (Y.ordinaryMap (f b)).val := by
    rw [hZ a,hZ b,hY (f a),hY (f b)]
    exact F.sameRV_iff a b
  exact ⟨relativePreparedMatchingOfTerminal Z Y f hf.bijective h00 C hC.surjective
    (D.plans_disc_paired hE hSource hTarget hf.bijective.injective) hOrdinary⟩

end DiamondIntegral.Section6
