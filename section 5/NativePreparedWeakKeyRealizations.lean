import «section 5».NativePreparedWeakFunctionalKeys
import «section 5».NativePreparedKeyRealizations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVCodeBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p k l q a : ℕ}

section Rows
variable {S : Set M} (C : DefSet (M := M) S p l) (hC : GammaSetDefinable B (carrier C))
variable (Z : GammaDomainFormula B ((p+l)+q) 0 (fun _ => .rv))
variable (F : GammaFiniteRVSchema B ((p+l)+q) a k (fun _ => .rv))
variable (Y : GammaGroundDefSet hc B (rawMixedSpace (M := M) (p+k) (l+(q+a))))
variable (hv : ∀ z ∈ rawDomain (nativePreparedParameterBase (hc := hc) C hC Z),F.valid z)
variable (hbase : ∀ w : Y,preparedFamilyBase w.val ∈ carrier C)
variable (hrow : ∀ (c : C) (v : Fin q → CanonicalRV.RVSort M)
  (y : Fin k → Section2.VF M) (u : Fin a → CanonicalRV.RVSort M),
  (Fin.append c.val.1 y,Fin.append c.val.2 (Fin.append v u)) ∈ Y.carrier ↔
    Fin.append (rawPreparedKey c.val) (rvValues v) ∈ rawDomain (nativePreparedParameterBase (hc := hc) C hC Z) ∧
      Fin.append (Fin.append (Fin.append (rawPreparedKey c.val) (rvValues v)) (rvValues u))
        (rvValues (Section2.tupleRV M y)) ∈ F.volume)

include hv hbase hrow in
theorem nativePreparedLiftKey_graphs_weak :
    (∀ u : (nativeMixedFullKeyMap Y).image,
      u.val ∘ preparedRVTotalIndices p k l q a ∈
        (originalRVTotalFamily (nativePreparedParameterBase (hc := hc) C hC Z) (finiteRVSchemaDomain F)).carrier) ∧
    (∀ u : (nativeMixedFullKeyMap Y).image,
      Fin.append (rvValues (u.val ∘ preparedRVTotalIndices p k l q a))
        (rvValues (u.val ∘ preparedRVFibreLabelIndices p k l q a)) ∈ F.volume) := by
  have H (u : (nativeMixedFullKeyMap Y).image) :
      u.val ∘ preparedRVTotalIndices p k l q a ∈
          (originalRVTotalFamily (nativePreparedParameterBase (hc := hc) C hC Z) (finiteRVSchemaDomain F)).carrier ∧
        Fin.append (rvValues (u.val ∘ preparedRVTotalIndices p k l q a))
          (rvValues (u.val ∘ preparedRVFibreLabelIndices p k l q a)) ∈ F.volume := by
    obtain ⟨w,hw⟩ := u.property
    have hk : (flatKey w.val).2 = u.val := hw
    let c : C := ⟨preparedFamilyBase w.val,hbase w⟩
    have hpacked : (Fin.append c.val.1 (preparedFamilyFibreVF w.val),
        Fin.append c.val.2 (Fin.append (preparedFamilyOldRV w.val) (preparedFamilyFibreRV w.val))) ∈ Y.carrier :=
      (preparedFamily_reconstruct w.val).symm ▸ w.property
    have hr := (hrow c (preparedFamilyOldRV w.val) (preparedFamilyFibreVF w.val) (preparedFamilyFibreRV w.val)).mp hpacked
    have hT : u.val ∘ preparedRVTotalIndices p k l q a =
        Fin.append (Fin.append (flatKey c.val).2 (preparedFamilyOldRV w.val)) (preparedFamilyFibreRV w.val) :=
      (congrArg (fun z => z ∘ preparedRVTotalIndices p k l q a) hk).symm.trans
        (preparedRVTotalIndices_key w.val)
    have hL : u.val ∘ preparedRVFibreLabelIndices p k l q a =
        Section2.tupleRV M (preparedFamilyFibreVF w.val) :=
      (congrArg (fun z => z ∘ preparedRVFibreLabelIndices p k l q a) hk).symm.trans
        (preparedRVFibreLabelIndices_key w.val)
    have hτ : rvValues (Fin.append (flatKey c.val).2 (preparedFamilyOldRV w.val)) =
        Fin.append (rawPreparedKey c.val) (rvValues (preparedFamilyOldRV w.val)) := rvValues_append _ _
    constructor
    · rw [hT]
      apply (originalRVTotalFamily_mem _ _ _).mpr
      refine ⟨?_,?_⟩
      · apply (rvValues_mem_rawDomain_iff _ _).mp
        have hpre : Fin.append (Fin.append (flatKey c.val).2 (preparedFamilyOldRV w.val))
            (preparedFamilyFibreRV w.val) ∘ Fin.castAdd a =
            Fin.append (flatKey c.val).2 (preparedFamilyOldRV w.val) :=
          funext (fun i => Fin.append_left _ _ i)
        exact (congrArg rvValues hpre).symm ▸ (hτ.symm ▸ hr.1)
      · have hsrc := (hv _ hr.1).2.2.1 _ _ hr.2
        rw [rvValues_append,hτ]
        exact hsrc
    · rw [hT,hL,rvValues_append,hτ]
      exact hr.2
  exact ⟨fun u => (H u).1,fun u => (H u).2⟩

include hv hrow in
theorem nativePreparedLiftKey_onto_weak :
    ∀ t : originalRVTotalFamily (nativePreparedParameterBase (hc := hc) C hC Z) (finiteRVSchemaDomain F),
      ∃ u : (nativeMixedFullKeyMap Y).image,u.val ∘ preparedRVTotalIndices p k l q a = t.val := by
  intro t
  have ht := (originalRVTotalFamily_mem _ _ t.val).mp t.property
  have hτ : rvValues (t.val ∘ Fin.castAdd a) ∈ rawDomain (nativePreparedParameterBase (hc := hc) C hC Z) :=
    ⟨t.val ∘ Fin.castAdd a,ht.1,rfl⟩
  obtain ⟨c,v,hvRV,he,_⟩ := nativePreparedParameterBase_representative C hC Z _ hτ
  let vRV : Fin q → CanonicalRV.RVSort M := fun i => ⟨v i,hvRV i⟩
  have heTyped : Fin.append (flatKey c.val).2 vRV = t.val ∘ Fin.castAdd a := by
    apply rvValues_injective
    rw [rvValues_append]
    exact he
  have hpack : Fin.append (rvValues (t.val ∘ Fin.castAdd a))
      (rvValues (t.val ∘ Fin.natAdd ((p+l)+q))) = rvValues t.val :=
    Fin.append_castAdd_natAdd (f := rvValues t.val)
  have hD : Fin.append (rvValues (t.val ∘ Fin.castAdd a))
      (rvValues (t.val ∘ Fin.natAdd ((p+l)+q))) ∈ F.domain := hpack.symm ▸ ht.2
  obtain ⟨z,hz,_⟩ := (hv _ hτ).2.1 _ hD
  have hzRV : ∀ i,iRV (z i) := fun i => by
    simpa only [Fin.append_right,sortEval,iRV] using F.volume_definable.proper _ hz (Fin.natAdd (((p+l)+q)+a) i)
  let zRV : Fin k → CanonicalRV.RVSort M := fun i => ⟨z i,hzRV i⟩
  obtain ⟨y,hy⟩ := Section2.tupleRV_surjective zRV
  let w : Point (M := M) (p+k) (l+(q+a)) :=
    (Fin.append c.val.1 y,Fin.append c.val.2 (Fin.append vRV (t.val ∘ Fin.natAdd ((p+l)+q))))
  have hw : w ∈ Y.carrier := by
    apply (hrow c vRV y (t.val ∘ Fin.natAdd ((p+l)+q))).mpr
    have heRaw : Fin.append (rawPreparedKey c.val) (rvValues vRV) = rvValues (t.val ∘ Fin.castAdd a) :=
      (rvValues_append _ _).symm.trans (congrArg rvValues heTyped)
    rw [heRaw,hy]
    exact ⟨hτ,hz⟩
  refine ⟨(nativeMixedFullKeyMap Y).toImage ⟨w,hw⟩,?_⟩
  change (flatKey w).2 ∘ preparedRVTotalIndices p k l q a = t.val
  exact (preparedRVTotalIndices_packed_key c.val vRV y _).trans
    ((congrArg (fun z => Fin.append z (t.val ∘ Fin.natAdd ((p+l)+q))) heTyped).trans
      (Fin.append_castAdd_natAdd (f := t.val)))
end Rows

end DiamondIntegral.Section5
