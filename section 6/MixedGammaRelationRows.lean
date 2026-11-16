import «section 6».RawGammaPresentation
import «section 6».MixedGammaCodeGraphs

/-! The full real-code Gamma row graph of an actual definable relation
on mixed points and Gamma. All representatives of a Gamma value are
retained, before applying finite-prefix/RV-tail uniform bounds. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}

def mixedGammaRelationRows
    (H : DefSet ((rawMixedSpace (M := M) n r).prod rawGammaPresentation) S)
    (x : Fin (n+r) → M) : Set (Gamma M) :=
  {γ | ∃ p : Mixed M n r,mixedTuple p=x ∧ (p,γ) ∈ H.carrier}

theorem mixedTuple_injective_full {p q : Mixed M n r} (h : mixedTuple p=mixedTuple q) : p=q := by
  apply Prod.ext
  · funext i
    apply Subtype.ext
    simpa only [mixedTuple,Fin.append_left,vfValues] using congrFun h (Fin.castAdd r i)
  · funext i
    apply Subtype.ext
    simpa only [mixedTuple,Fin.append_right,rvValues] using congrFun h (Fin.natAdd n i)

theorem mixedGammaRelationRows_at
    (H : DefSet ((rawMixedSpace (M := M) n r).prod rawGammaPresentation) S)
    (p : Mixed M n r) (γ : Gamma M) :
    γ ∈ mixedGammaRelationRows H (mixedTuple p) ↔ (p,γ) ∈ H.carrier := by
  constructor
  · rintro ⟨q,hqp,hH⟩
    have he : q=p := mixedTuple_injective_full hqp
    exact he ▸ hH
  · exact fun h => ⟨p,rfl,h⟩

theorem mixedGammaRelationRows_definable
    (H : DefSet ((rawMixedSpace (M := M) n r).prod rawGammaPresentation) S)
    (E : DefSet (rawMixedSpace (M := M) n r) S)
    (hSource : ∀ z ∈ H.carrier,z.1 ∈ E.carrier) :
    S.Definable LRV (rawGammaFamilyGraph (mixedTuple '' E.carrier) (mixedGammaRelationRows H)) := by
  let P := rawMixedSpace (M := M) n r
  let Q := rawGammaPresentation (M := M)
  let idx : (Fin n ⊕ Fin r) ⊕ Fin 1 → Fin (n+r) ⊕ Fin 1 :=
    Sum.elim (Sum.elim (fun i => Sum.inl (Fin.castAdd r i)) (fun j => Sum.inl (Fin.natAdd n j))) Sum.inr
  have h := H.definable.preimage_comp idx
  change S.Definable LRV {z | z ∘ idx ∈ (P.prod Q).preimage H.carrier} at h
  convert h using 1
  ext z
  constructor
  · rintro ⟨hzD,hzNZ,p,hp,hH⟩
    have hCodes : z ∘ idx=Sum.elim (mixedValues p) (fun _ : Fin 1 => z (.inr 0)) := by
      funext i
      rcases i with (i | i) | i
      · simpa only [idx,Function.comp_apply,Sum.elim_inl,mixedTuple,mixedValues,Fin.append_left,vfValues]
          using (congrFun hp (Fin.castAdd r i)).symm
      · simpa only [idx,Function.comp_apply,Sum.elim_inl,Sum.elim_inr,mixedTuple,mixedValues,Fin.append_right,rvValues]
          using (congrFun hp (Fin.natAdd n i)).symm
      · fin_cases i
        rfl
    change z ∘ idx ∈ (P.prod Q).preimage H.carrier
    rw [hCodes]
    refine ⟨⟨mixedValues_mem_domain p,hzNZ⟩,?_⟩
    change (P.decode ⟨mixedValues p,mixedValues_mem_domain p⟩,
      GammaParameters.codeValue (z (.inr 0))) ∈ H.carrier
    simpa only [P,decode_mixedValues] using hH
  · rintro ⟨hzDom,hH⟩
    let p := P.decode ⟨(z ∘ idx) ∘ Sum.inl,hzDom.1⟩
    have hTuple : mixedTuple p=z ∘ Sum.inl := by
      have hCodes := mixedValues_decode (⟨(z ∘ idx) ∘ Sum.inl,hzDom.1⟩ : P.domain)
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa only [p,P,idx,Function.comp_apply,Sum.elim_inl,mixedTuple,mixedValues,Fin.append_left,vfValues]
          using congrFun hCodes (Sum.inl j)
      · simpa only [p,P,idx,Function.comp_apply,Sum.elim_inl,Sum.elim_inr,mixedTuple,mixedValues,Fin.append_right,rvValues]
          using congrFun hCodes (Sum.inr j)
    have hH' : (p,GammaParameters.codeValue (z (.inr 0))) ∈ H.carrier := hH
    refine ⟨⟨p,hSource _ hH',hTuple⟩,hzDom.2,p,hTuple,hH'⟩

end DiamondIntegral.Section6
