import «section 3».GammaMixedFinitePartitionValues
import «section 3».GammaFullMeasuredUnaryPartition
import «section 3».GammaMixedContractionValues

/-! Binary additivity for arbitrary mixed Gamma forms descends through
the actual VF-fixed retained presentation and its corresponding domain
predicates. No measure representative is added to the ground. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaMixed_full_bijection_values
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hg : Cardinal.mk B.gamma < C.κ) (hNames : commonRealNames B ⊆ (C.base : Set M))
    (hGenerated : VFGammaGeneratedBase B)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    {U V : GammaGroundMeasuredVFData hc B (n+1)} (F : GammaFullMeasuredBijection U V) :
    gammaMixedContractionValue C hBC hv hNames hGenerated U =
      gammaMixedContractionValue C hBC hv hNames hGenerated V := by
  let hr := (Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small
  obtain ⟨Q,hQ⟩ := gammaFullMeasured_unary_partition C.uncountable.le C.saturated C.model00 hr hv δ hδ1 F
  let ι := ↥Q.pieces
  have hPieces := fun i : ι => hQ i.val i.property
  choose D hD hDV T hT using hPieces
  let P : ι → GammaGroundDefSet hc B (rawMixedSpace (M := M) (n+1) U.arity) :=
    fun i => Section5.nativeGammaPointDomain i.val (Q.definable i.val i.property)
  let R : ι → GammaGroundDefSet hc B (rawMixedSpace (M := M) (n+1) V.arity) :=
    fun i => Section5.nativeGammaPointDomain (D i) (hD i)
  let hP : ∀ i, (P i).carrier ⊆ U.domain.carrier := fun i => Q.subset i.val i.property
  let hR : ∀ i, (R i).carrier ⊆ V.domain.carrier := hDV
  have hDisjP : ∀ i ∈ (Finset.univ : Finset ι), ∀ j ∈ (Finset.univ : Finset ι),
      i ≠ j → Disjoint (P i).carrier (P j).carrier := by
    intro i _ j _ hij
    exact Q.disjoint i.val i.property j.val j.property (fun h => hij (Subtype.ext h))
  have hCoverP : ∀ p : U.domain, ∃ i ∈ (Finset.univ : Finset ι), p.val ∈ (P i).carrier := by
    intro p
    obtain ⟨A,hA,hp⟩ := Q.cover p
    exact ⟨⟨A,hA⟩,Finset.mem_univ _,hp⟩
  have hDisjR : ∀ i ∈ (Finset.univ : Finset ι), ∀ j ∈ (Finset.univ : Finset ι),
      i ≠ j → Disjoint (R i).carrier (R j).carrier := by
    intro i _ j _ hij
    apply Set.disjoint_left.mpr
    intro q hqi hqj
    obtain ⟨x,hx⟩ := ((T i).fullMap C.uncountable.le C.saturated hr hv).map.bijective.2 ⟨q,hqi⟩
    obtain ⟨y,hy⟩ := ((T j).fullMap C.uncountable.le C.saturated hr hv).map.bijective.2 ⟨q,hqj⟩
    let xu : U.domain := ⟨x.val,hP i x.property⟩
    let yu : U.domain := ⟨y.val,hP j y.property⟩
    have hxF : (F.map.map xu).val = q :=
      (hT i x).symm.trans (congrArg (fun p : (V.restrict (R i) (hR i)).domain => p.val) hx)
    have hyF : (F.map.map yu).val = q :=
      (hT j y).symm.trans (congrArg (fun p : (V.restrict (R j) (hR j)).domain => p.val) hy)
    have hxy : xu = yu := F.map.bijective.1 (Subtype.ext (hxF.trans hyF.symm))
    have he : x.val = y.val := congrArg (fun p : U.domain => p.val) hxy
    exact Set.disjoint_left.mp (Q.disjoint i.val i.property j.val j.property
      (fun h => hij (Subtype.ext h))) x.property (he.symm ▸ y.property)
  have hCoverR : ∀ q : V.domain, ∃ i ∈ (Finset.univ : Finset ι), q.val ∈ (R i).carrier := by
    intro q
    let p := F.map.symm.map q
    have hpq : F.map.map p = q := F.map.map.apply_inverse F.map.bijective q
    obtain ⟨A,hA,hpA⟩ := Q.cover p
    let i : ι := ⟨A,hA⟩
    let a : P i := ⟨p.val,hpA⟩
    let b := ((T i).fullMap C.uncountable.le C.saturated hr hv).map.map a
    have hb : b.val = q.val := (hT i a).trans (congrArg (fun q : V.domain => q.val) hpq)
    exact ⟨i,Finset.mem_univ _,hb ▸ b.property⟩
  have hSource := gammaMixed_finite_partition_values C hBC hv hg hNames hGenerated δ hδ hδ1
    Finset.univ U P hP hDisjP hCoverP
  have hTarget := gammaMixed_finite_partition_values C hBC hv hg hNames hGenerated δ hδ hδ1
    Finset.univ V R hR hDisjR hCoverR
  apply hSource.trans
  apply Eq.trans _ hTarget.symm
  apply Finset.sum_congr rfl
  intro i _
  exact gammaMixed_unary_chain_contraction_values C hBC hv hNames hGenerated hg δ hδ hδ1 (T i)

end DiamondIntegral.Section3
