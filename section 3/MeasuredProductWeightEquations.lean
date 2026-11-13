import «section 3».MonomialTensorLocalMatches
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {r m : ℕ}
variable {P Q : Space LRV M} {U0 : GammaGroundDefSet hc B P} {V0 : GammaGroundDefSet hc B Q}

/-- On normalized native charts, the actual global weight equation
implies the required Gamma weight transport on every full monomial
rectangle. A residue point is only a proof witness. -/
theorem gammaGroundMonomialPatch_weight_equation
    (F : GammaGroundBijection U0 V0) (wU : U0 → Values.Gamma (M := M)) (wV : V0 → Values.Gamma (M := M))
    (hF : ∀ a, wU a = wV (F.map a))
    (X Y : GammaGroundRESUnitChart hc B r) (G H : GammaGroundGammaPiece hc B m)
    (s : GammaGroundMap (gammaGroundNativeProductDomain X G) U0)
    (t : GammaGroundMap (gammaGroundNativeProductDomain Y H) V0)
    (u v : (Fin m → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hs : ∀ z, wU (s z) = u (rvUnitTupleValues z.val.1))
    (ht : ∀ z, wV (t z) = v (rvUnitTupleValues z.val.1))
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace m).prod (rawRVUnitSpace X.arity)))
    (f : GammaGroundMap T (gammaGroundRVUnitGammaPreimage H)) (g : GammaGroundMap T Y.native)
    (hT : T.carrier ⊆ (gammaGroundNativeProductDomain X G).carrier)
    (hgraph : ∀ a : T, t ⟨((f a).val,(g a).val),(f a).property,(g a).property⟩ = F.map (s ⟨a.val,hT a.property⟩))
    (E : GammaGroundRVProductMonomialPatch X.native T (gammaGroundRVUnitGammaPreimage H) Y.native f g) :
    ∀ γ : Fin m → Values.Gamma (M := M), γ ∈ E.gamma.carrier →
      u γ = v (fun i => E.value i * integerMonomialMap E.matrix γ i) := by
  intro γ hγ
  obtain ⟨a,ha⟩ := E.residue_nonempty
  let ar : E.residue := ⟨a,ha⟩
  obtain ⟨x,hx⟩ := rvUnitTupleValues_surjective m γ
  have hxG : rvUnitTupleValues x ∈ E.gamma.carrier := hx.symm ▸ hγ
  obtain ⟨z,hz,hfz,_⟩ := E.formula ar x hxG
  let p : gammaGroundNativeProductDomain X G := ⟨z.val,hT z.property⟩
  let q : gammaGroundNativeProductDomain Y H := ⟨((f z).val,(g z).val),(f z).property,(g z).property⟩
  have he : u (rvUnitTupleValues z.val.1) = v (rvUnitTupleValues (f z).val) :=
    (hs p).symm.trans ((hF (s p)).trans ((congrArg wV (hgraph z)).symm.trans (ht q)))
  have hp : rvUnitTupleValues z.val.1 = γ :=
    (congrArg (fun p : (Fin m → (CanonicalRV.RVSort M)ˣ) × (Fin X.arity → (CanonicalRV.RVSort M)ˣ) => rvUnitTupleValues p.1) hz).trans hx
  have hm : rvUnitTupleValues (integerMonomialMap E.matrix x) = integerMonomialMap E.matrix γ :=
    (monomial_map_value (rvUnitValueHom (M := M)) E.matrix x).trans (congrArg (integerMonomialMap E.matrix) hx)
  have hq : rvUnitTupleValues (f z).val = fun i => E.value i * integerMonomialMap E.matrix γ i := by
    calc
      _ = rvUnitTupleValues (fun i => (E.coefficient ar).val i * integerMonomialMap E.matrix x i) :=
        congrArg rvUnitTupleValues hfz
      _ = _ := by
        funext i
        change rvUnitValueHom ((E.coefficient ar).val i * integerMonomialMap E.matrix x i) = _
        rw [map_mul]
        exact congrArg₂ (fun a b : Values.Gamma (M := M) => a*b)
          (congrFun (E.coefficient_values ar) i) (congrFun hm i)
  exact (congrArg u hp).symm.trans (he.trans (congrArg v hq))
end DiamondIntegral.Section3
