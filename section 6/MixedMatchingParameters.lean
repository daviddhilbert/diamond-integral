import «section 6».FiniteMatchingExceptions

/-! Actual paired matching parameters retain both VF center coordinates
and every old source and target RV label. Their complete original-base
graph is constructed, and the exceptional parameter domain is finite. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r s : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S} {B : DefSet (rawMixedSpace (M := M) 1 s) S}

def unaryMatchingParameterMap (f : Map A B) : Map A (DefSet.univ (rawMixedSpace (M := M) 2 (r+s)) S) := by
  let P := (rawMixedSpace (M := M) 1 r).prod (rawMixedSpace (M := M) 1 s)
  let pairPoint (p : P.Carrier) : Mixed M 2 (r+s) :=
    (![p.1.1 0,p.2.1 0],Fin.append p.1.2 p.2.2)
  let F (z : ((Fin 1 ⊕ Fin r) ⊕ (Fin 1 ⊕ Fin s)) → M) : Fin 2 ⊕ Fin (r+s) → M :=
    Sum.elim (![z (.inl (.inl 0)),z (.inr (.inl 0))])
      (Fin.append (fun i => z (.inl (.inr i))) (fun i => z (.inr (.inr i))))
  have hCode (c : P.domain) : mixedValues (pairPoint (P.decode c))=F c.val := by
    have hLeft := mixedValues_decode
      (⟨c.val ∘ Sum.inl,c.property.1⟩ : (rawMixedSpace (M := M) 1 r).domain)
    have hRight := mixedValues_decode
      (⟨c.val ∘ Sum.inr,c.property.2⟩ : (rawMixedSpace (M := M) 1 s).domain)
    funext i
    cases i with
    | inl i =>
      fin_cases i
      · exact congrFun hLeft (.inl 0)
      · exact congrFun hRight (.inl 0)
    | inr i =>
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa only [F,pairPoint,mixedValues,Sum.elim_inr,rvValues,Fin.append_left,Function.comp_apply,P,Space.prod] using (congrFun hLeft (.inr j) : _)
      · simpa only [F,pairPoint,mixedValues,Sum.elim_inr,rvValues,Fin.append_right,Function.comp_apply,P,Space.prod] using (congrFun hRight (.inr j) : _)
  have hF : S.DefinableMap LRV F := by
    rintro (i | i)
    · fin_cases i <;> exact Set.DefinableFun.proj LRV
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa only [F,Sum.elim_inr,Fin.append_left] using
          (Set.DefinableFun.proj (L := LRV) (A := S) (i := (Sum.inl (Sum.inr j) : (Fin 1 ⊕ Fin r) ⊕ (Fin 1 ⊕ Fin s))))
      · simpa only [F,Sum.elim_inr,Fin.append_right] using
          (Set.DefinableFun.proj (L := LRV) (A := S) (i := (Sum.inr (Sum.inr j) : (Fin 1 ⊕ Fin r) ⊕ (Fin 1 ⊕ Fin s))))
  let H : Map (A.prod B) (DefSet.univ (rawMixedSpace (M := M) 2 (r+s)) S) :=
    Map.ofCodes (A.prod B) pairPoint F hF
      (fun c => (hCode c) ▸ mixedValues_mem_domain (pairPoint (P.decode c)))
      (by intro c; apply mixedValues_injective; exact (mixedValues_decode _).trans (hCode c).symm)
  exact H.comp ((Map.id A).pair f)

theorem unaryMatchingParameterMap_value (f : Map A B) (p : A) :
    (unaryMatchingParameterMap f p).val=(![p.val.1 0,(f p).val.1 0],Fin.append p.val.2 (f p).val.2) := rfl

def pairedUnaryExceptionParameters (f : Map A B)
    (E : DefSet (rawMixedSpace (M := M) 1 r) S) (F : DefSet (rawMixedSpace (M := M) 1 s) S)
    (hEA : E.carrier ⊆ A.carrier) : DefSet (rawMixedSpace (M := M) 2 (r+s)) S :=
  ((unaryMatchingParameterMap f).restrict (pairedUnaryExceptionDomain_subset f E F hEA)).image

theorem pairedUnaryExceptionParameters_finite
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (f : Map A B) (hf : Function.Bijective f)
    (E : DefSet (rawMixedSpace (M := M) 1 r) S) (F : DefSet (rawMixedSpace (M := M) 1 s) S)
    (hEA : E.carrier ⊆ A.carrier)
    (hE : (Prod.fst '' E.carrier).Finite) (hF : (Prod.fst '' F.carrier).Finite)
    (hFinite : ∀ a : Fin 1 → VF M,{u : Fin r → RVInfinity M | (a,u) ∈ A.carrier}.Finite) :
    (pairedUnaryExceptionParameters f E F hEA).carrier.Finite := by
  have hZ := pairedUnaryExceptionDomain_finite hc hκ hs hsmall f hf E F hEA hE hF hFinite
  letI : Fintype (pairedUnaryExceptionDomain f E F) := hZ.fintype
  exact Set.finite_range _

end DiamondIntegral.Section6
