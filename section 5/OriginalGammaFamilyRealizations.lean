import «section 5».RVGammaFamilyLifts

/-! Original domain schemata realize actual mixed RV/Gamma families by
taking full nonzero code images. The original base is unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p n : ℕ}

theorem allRVGammaDomain_definable (D : GammaDomainFormula B p n (fun _ => .rv)) :
    DefinableOverBase B (fun _ => .rv) D.val := by
  convert D.property using 1
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp only [Fin.append_left,Fin.append_right]

def originalGammaFamilyCodeDomain
    (X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) p))
    (D : GammaDomainFormula B p n (fun _ => .rv)) :
    GammaGroundDefSet hc B (rawRVUnitSpace (M := M) (p+n)) :=
  (gammaGroundRVUnitSetOfBase D.val (allRVGammaDomain_definable D)).inter
    ⟨{u | u ∘ Fin.castAdd n ∈ X.carrier}, X.definable.preimage
      ((universalProductFst (rawRVUnitSpace p) ((volumeGammaSpace hc).power (Fin n)) B.real).comp
        (unitMixedGammaMap hc B.real p n))⟩

def originalGammaFamilyRealization
    (X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) p))
    (D : GammaDomainFormula B p n (fun _ => .rv)) :
    GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) p).prod ((volumeGammaSpace hc).power (Fin n))) :=
  (GammaGroundMap.ofGlobal (originalGammaFamilyCodeDomain X D)
    (GammaGroundDefSet.univ hc B ((rawRVUnitSpace p).prod ((volumeGammaSpace hc).power (Fin n))))
    (unitMixedGammaMap hc B.real p n) (fun _ => Set.mem_univ _)).image

theorem originalGammaFamilyRealization_projection
    (X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) p))
    (D : GammaDomainFormula B p n (fun _ => .rv))
    (x : Fin p → (CanonicalRV.RVSort M)ˣ) (γ : Fin n → Values.Gamma (M := M))
    (h : (x,γ) ∈ (originalGammaFamilyRealization X D).carrier) : x ∈ X.carrier := by
  obtain ⟨u, hu⟩ := h
  have he : u.val ∘ Fin.castAdd n = x := congrArg Prod.fst hu
  exact he ▸ u.property.2

theorem originalGammaFamilyRealization_row
    (X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) p))
    (D : GammaDomainFormula B p n (fun _ => .rv))
    (hD : ∀ x : X, originalGammaSourceValid hc D (rvUnitValues x.val))
    (x : X) (γ : Fin n → Values.Gamma (M := M)) :
    (x.val,γ) ∈ (originalGammaFamilyRealization X D).carrier ↔
      γ ∈ originalGammaSourceRow hc D (rvUnitValues x.val) := by
  have hrep := originalGammaSourceRow_represents hc D (rvUnitValues x.val) (hD x)
  constructor
  · rintro ⟨u, hu⟩
    have hx : u.val ∘ Fin.castAdd n = x.val := congrArg Prod.fst hu
    have hv : rvUnitTupleValues (u.val ∘ Fin.natAdd p) = γ := congrArg Prod.snd hu
    let v := rvUnitValues (u.val ∘ Fin.natAdd p)
    have hp : ∀ j, NonzeroRV (v j) :=
      (Set.ext_iff.mp rvUnitValues_range v).mp ⟨u.val ∘ Fin.natAdd p,rfl⟩
    have hq : codeValue ∘ v = γ := by
      have he : codeValue ∘ v = rvUnitTupleValues (u.val ∘ Fin.natAdd p) := by
        funext j
        exact codeValue_raw ⟨(u.val (Fin.natAdd p j)).val,(fun h => (u.val (Fin.natAdd p j)).ne_zero (Subtype.ext (h.trans RVOperations.zero_val.symm)))⟩
      exact he.trans hv
    apply hq ▸ ((hrep v).mp ?_).2
    rw [gammaDomainSyntax_realize]
    have he : Fin.append (rvUnitValues x.val) v = rvUnitValues u.val := by
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [Fin.append_left]
        exact congrArg (fun t : Fin p → (CanonicalRV.RVSort M)ˣ => rvUnitValues t j) hx.symm
      · simp only [Fin.append_right]
        rfl
    exact he.symm ▸ u.property.1
  · intro hγ
    obtain ⟨v,hp,hq⟩ := gamma_tuple_code_surjective γ
    have hv := (hrep v).mpr ⟨hp,hq.symm ▸ hγ⟩
    obtain ⟨t,ht⟩ := (Set.ext_iff.mp rvUnitValues_range v).mpr hp
    let u := Fin.append x.val t
    have hraw : rvUnitValues u = Fin.append (rvUnitValues x.val) v := by
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [u,rvUnitValues,Fin.append_left]
      · simpa only [u,rvUnitValues,Fin.append_right] using congrFun ht j
    have hx : u ∘ Fin.castAdd n = x.val := by funext i; exact Fin.append_left _ _ _
    have hval : rvUnitTupleValues (u ∘ Fin.natAdd p) = γ := by
      calc
        rvUnitTupleValues (u ∘ Fin.natAdd p) = codeValue ∘ v := by
          funext j
          have he := codeValue_raw ⟨(t j).val,(fun h => (t j).ne_zero (Subtype.ext (h.trans RVOperations.zero_val.symm)))⟩
          change rvUnitValueHom (Fin.append x.val t (Fin.natAdd p j)) = codeValue (v j)
          rw [Fin.append_right]
          rw [← congrFun ht j]
          exact he.symm
        _ = γ := hq
    have humem : u ∈ (originalGammaFamilyCodeDomain X D).carrier := by
      refine ⟨?_,?_⟩
      · change rvUnitValues u ∈ D.val
        rw [hraw]
        exact (gammaDomainSyntax_realize hc B D (rvUnitValues x.val) v).mp hv
      · change u ∘ Fin.castAdd n ∈ X.carrier
        exact hx.symm ▸ x.property
    exact ⟨⟨u,humem⟩,Prod.ext hx hval⟩

end DiamondIntegral.Section5
