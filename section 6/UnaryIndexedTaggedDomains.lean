import «section 6».UnaryIndexedFamilyGeometry
import «section 6».PureRVDiscQuotients
import «section 6».CentripetalFocusProjection

/-! Reassembled ambient domains retain their leading terms on each
old-label fibre. Prepared subdomains therefore have actual whole-label
loci, including the active focus domain of the next component. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ}
variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}

theorem unaryIndexedMixedFamily_tagged
    (hB : ∀ b ∈ B.carrier,∀ c ∈ B.carrier,b.2=c.2 → tupleRV M b.1=tupleRV M c.1)
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    (T : MixedSetParameterTemplate (M := M) S 1 n s)
    (hFibres : ∀ b : B,IsRVPullback (T.fibre (unaryFamilyParameter η b)).carrier)
    (hRows : ∀ b c : B,b.val.2=c.val.2 →
      ((leadingRVImageTemplate T).fibre (unaryFamilyParameter η b)).carrier=
        ((leadingRVImageTemplate T).fibre (unaryFamilyParameter η c)).carrier)
    (hTagged : ∀ b : B,∀ x ∈ (T.fibre (unaryFamilyParameter η b)).carrier,
      ∀ y ∈ (T.fibre (unaryFamilyParameter η b)).carrier,x.2=y.2 → tupleRV M x.1=tupleRV M y.1) :
    ∀ p ∈ (unaryIndexedMixedFamily η T).carrier,∀ q ∈ (unaryIndexedMixedFamily η T).carrier,
      p.2=q.2 → tupleRV M p.1=tupleRV M q.1 := by
  intro p hp q hq hRV
  obtain ⟨b,hb,hpT⟩ := (mem_unaryIndexedMixedFamily η T p).mp hp
  obtain ⟨c,hc,hqT⟩ := (mem_unaryIndexedMixedFamily η T q).mp hq
  have hTags : b.val.2=c.val.2 := by
    rw [← hb,← hc]
    exact congrArg (fun u => u ∘ Fin.castAdd s) hRV
  have hHead := congrFun (hB b.val b.property c.val c.property hTags) 0
  have hFibresEq := template_fibres_eq_of_leading_rows T _ _ (hFibres b) (hFibres c) (hRows b c hTags)
  rw [hFibresEq] at hpT
  have hTail := hTagged c _ hpT _ hqT (congrArg (fun u => u ∘ Fin.natAdd r) hRV)
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [← hb,← hc] at hHead
    exact hHead
  · exact congrFun hTail j

theorem rvPullback_subdomain_eq_focusActive
    {A C : DefSet (rawMixedSpace (M := M) n r) S}
    (hCA : C.carrier ⊆ A.carrier) (hC : IsRVPullback C.carrier)
    (hTag : ∀ p ∈ A.carrier,∀ q ∈ A.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1) :
    C=focusActive A (pureRVTagDomain C) := by
  apply defSet_eq_of_carrier_eq
  ext p
  constructor
  · intro hp
    exact ⟨hCA hp,⟨⟨p,hp⟩,rfl⟩⟩
  · rintro ⟨hp,⟨q,hq⟩⟩
    have hRV : q.val.2=p.2 := hq
    exact rvPullback_mem_of_sameRV hC q.property
      (hTag q.val (hCA q.property) p hp hRV) hRV

end DiamondIntegral.Section6
