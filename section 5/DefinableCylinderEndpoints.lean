import «section 5».GeneralEndpointMaps
import «section 5».GroundSpaceQuantifiers
import «section 5».CylinderEndpointUniqueness
import «section 5».EndpointFamilyLifts

/-! The unique endpoints of a definable cylindrical fibre form actual
maps over the original base. No endpoint representatives are named. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3
open IntegrationInACVF.Section3ACVF
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {Q : Space LRV M}

theorem gammaEndpointCondition_definable (shape : CylinderFibreKind) :
    GammaGroundDefinable hc B (((volumeGammaSpace hc).power (Fin shape.endpoints)).prod (volumeGammaSpace hc))
      {p | shape.condition (Γ := Values.Gamma (M := M)) p.1 p.2} := by
  let A := GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin shape.endpoints))
  let f : Fin shape.endpoints → GammaGroundMap A (GammaGroundDefSet.univ hc B (volumeGammaSpace hc)) :=
    fun j => GammaGroundMap.ofGlobal _ _ (universalPowerCoordinate (volumeGammaSpace hc) B.real j) (fun _ => Set.mem_univ _)
  have hh := ((generalEndpointTupleMap shape f).preimage (endpointConditionSet shape)).definable
  apply hh.congr
  intro p
  have hvalue (a : A.prod (GammaGroundDefSet.univ hc B (volumeGammaSpace hc))) :
      (generalEndpointTupleMap shape f a).val ∈ (endpointConditionSet (hc := hc) (B := B) shape).carrier ↔
        shape.condition (Γ := Values.Gamma (M := M)) a.val.1 a.val.2 := by
    rw [generalEndpointTupleMap_value]
    change shape.condition (Γ := Values.Gamma (M := M)) _ _ ↔ _
    have hi : (Fin.snoc (α := fun _ : Fin (shape.endpoints+1) => Values.Gamma (M := M)) a.val.1 a.val.2) ∘ Fin.castSucc = a.val.1 := by
      funext j; simp only [Function.comp_def, Fin.snoc_castSucc]
    change shape.condition (Γ := Values.Gamma (M := M))
      ((Fin.snoc (α := fun _ : Fin (shape.endpoints+1) => Values.Gamma (M := M)) a.val.1 a.val.2) ∘ Fin.castSucc)
      ((Fin.snoc (α := fun _ : Fin (shape.endpoints+1) => Values.Gamma (M := M)) a.val.1 a.val.2) (Fin.last shape.endpoints)) ↔ _
    rw [hi, Fin.snoc_last]
  constructor
  · rintro ⟨a,ha,hc⟩
    exact ha ▸ (hvalue a).mp hc
  · intro hc
    exact ⟨⟨p,Set.mem_univ _,Set.mem_univ _⟩,rfl,(hvalue _).mpr hc⟩

theorem gammaEndpointOrdered_definable (shape : CylinderFibreKind) :
    GammaGroundDefinable hc B ((volumeGammaSpace hc).power (Fin shape.endpoints))
      {a | shape.ordered (Γ := Values.Gamma (M := M)) a} := by
  apply gammaGroundGammaPower_predicate_definable
  cases shape with
  | band => exact FullGammaSyntax.lt_definable _ (0 : Fin 2) 1
  | graph => exact FullGammaSyntax.Definable.true_ _
  | upperRay => exact FullGammaSyntax.Definable.true_ _
  | lowerRay => exact FullGammaSyntax.Definable.true_ _
  | line => exact FullGammaSyntax.Definable.true_ _

theorem cylinderEndpointGraph_definable
    (X : GammaGroundDefSet hc B Q) (shape : CylinderFibreKind)
    (T : GammaGroundDefSet hc B (Q.prod (volumeGammaSpace hc))) :
    GammaGroundDefinable hc B (Q.prod ((volumeGammaSpace hc).power (Fin shape.endpoints)))
      {p | p.1 ∈ X.carrier ∧ shape.ordered (Γ := Values.Gamma (M := M)) p.2 ∧
        ∀ γ : Values.Gamma (M := M), (p.1,γ) ∈ T.carrier ↔ shape.condition (Γ := Values.Gamma (M := M)) p.2 γ} := by
  let G := (volumeGammaSpace hc).power (Fin shape.endpoints)
  let P := Q.prod G
  let fst := universalProductFst P (volumeGammaSpace hc) B.real
  let snd := universalProductSnd P (volumeGammaSpace hc) B.real
  let toT := (((universalProductFst Q G B.real).comp fst).pair snd).toUniv
  let toC := (((universalProductSnd Q G B.real).comp fst).pair snd).toUniv
  have ht := T.definable.preimage toT
  have hcnd := (gammaEndpointCondition_definable (hc := hc) (B := B) shape).preimage toC
  have hall := ground_space_forall_right (ground_space_iff_definable ht hcnd)
  have hX := X.definable.preimage (universalProductFst Q G B.real)
  have ho := (gammaEndpointOrdered_definable (hc := hc) (B := B) shape).preimage (universalProductSnd Q G B.real)
  exact hX.inter (ho.inter hall)

theorem definable_cylinder_endpoints
    (X : GammaGroundDefSet hc B Q) (shape : CylinderFibreKind)
    (T : GammaGroundDefSet hc B (Q.prod (volumeGammaSpace hc)))
    (hfibre : ∀ x : X, shape.Describes (fun γ : Values.Gamma (M := M) => (x.val,γ) ∈ T.carrier)) :
    ∃ f : Fin shape.endpoints → GammaGroundMap X (GammaGroundDefSet.univ hc B (volumeGammaSpace hc)),
      (∀ x : X, shape.ordered (Γ := Values.Gamma (M := M)) (fun j => (f j x).val)) ∧
      ∀ x : X, ∀ γ : Values.Gamma (M := M), (x.val,γ) ∈ T.carrier ↔ shape.condition (Γ := Values.Gamma (M := M)) (fun j => (f j x).val) γ := by
  choose a ha hrow using hfibre
  let F : GammaGroundMap X (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin shape.endpoints))) := {
    toFun := fun x => ⟨a x,Set.mem_univ _⟩
    graph_definable := by
      apply (cylinderEndpointGraph_definable X shape T).congr
      intro p
      constructor
      · rintro ⟨hx,ho,hr⟩
        let x : X := ⟨p.1,hx⟩
        have he : a x = p.2 := shape.endpoints_unique _ _ (ha x) ho (fun γ => (hrow x γ).symm.trans (hr γ))
        exact ⟨x,rfl,he⟩
      · rintro ⟨x,hx,hf⟩
        change a x = p.2 at hf
        exact ⟨hx ▸ x.property, hf ▸ ha x, fun γ => by rw [← hx, ← hf]; exact hrow x γ⟩ }
  let f : Fin shape.endpoints → GammaGroundMap X (GammaGroundDefSet.univ hc B (volumeGammaSpace hc)) :=
    fun j => (GammaGroundMap.ofGlobal _ _ (universalPowerCoordinate (volumeGammaSpace hc) B.real j)
      (fun _ => Set.mem_univ _)).comp F
  exact ⟨f,ha,hrow⟩

end DiamondIntegral.Section5
