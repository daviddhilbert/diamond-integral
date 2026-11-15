import «section 5».RVGammaReverseLifts
import «section 5».NativeDescribedCylinderFubini

/-! Adding the first Gamma coordinate of a cylindrical cell amounts to
adding the last RV representative after reversing the Gamma-code block. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p n : ℕ}

def unitGammaHeadFamilyMap (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) (p n : ℕ) :
    GammaGroundMap
      (GammaGroundDefSet.univ hc B ((rawRVUnitSpace (M := M) (p+n)).prod (volumeGammaSpace hc)))
      (GammaGroundDefSet.univ hc B ((rawRVUnitSpace (M := M) p).prod ((volumeGammaSpace hc).power (Fin (n+1))))) := by
  let U := GammaGroundDefSet.univ hc B ((rawRVUnitSpace (M := M) (p+n)).prod (volumeGammaSpace hc))
  let fst := universalProductFst (rawRVUnitSpace (M := M) (p+n)) (volumeGammaSpace hc) B.real
  let base : GammaGroundMap U (GammaGroundDefSet.univ hc B (rawRVUnitSpace (M := M) p)) :=
    GammaGroundMap.ofGlobal _ _ ((unitTupleReindexMap B.real (Fin.castAdd n)).comp fst) (fun _ => Set.mem_univ _)
  let output : GammaGroundMap U (GammaGroundDefSet.univ hc B (volumeGammaSpace hc)) :=
    GammaGroundMap.ofGlobal _ _ (universalProductSnd (rawRVUnitSpace (M := M) (p+n)) (volumeGammaSpace hc) B.real) (fun _ => Set.mem_univ _)
  let previous (j : Fin n) : GammaGroundMap U (GammaGroundDefSet.univ hc B (volumeGammaSpace hc)) :=
    GammaGroundMap.ofGlobal _ _
      (((universalPowerCoordinate (volumeGammaSpace hc) B.real (Fin.natAdd p j.rev)).comp
        (rvUnitGammaMap hc B.real (p+n))).comp fst) (fun _ => Set.mem_univ _)
  exact (base.pair (GammaGroundMap.tuple (fun i => Fin.cases output previous i))).toUniv

theorem unitGammaHeadFamilyMap_value
    (a : GammaGroundDefSet.univ hc B ((rawRVUnitSpace (M := M) (p+n)).prod (volumeGammaSpace hc))) :
    (unitGammaHeadFamilyMap hc B p n a).val =
      (a.val.1 ∘ Fin.castAdd n,
        Fin.cons a.val.2 (rvUnitTupleValues (a.val.1 ∘ Fin.natAdd p ∘ Fin.rev))) := by
  apply Prod.ext
  · rfl
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

def rvGammaHeadFamily
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) p).prod ((volumeGammaSpace hc).power (Fin (n+1))))) :=
  (unitGammaHeadFamilyMap hc B p n).preimage T

theorem rvGammaHeadFamily_mem
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) p).prod ((volumeGammaSpace hc).power (Fin (n+1)))))
    (u : Fin (p+n) → (CanonicalRV.RVSort M)ˣ) (γ : Values.Gamma (M := M)) :
    (u,γ) ∈ (rvGammaHeadFamily T).carrier ↔
      (u ∘ Fin.castAdd n, Fin.cons γ (rvUnitTupleValues (u ∘ Fin.natAdd p ∘ Fin.rev))) ∈ T.carrier := by
  constructor
  · rintro ⟨a,ha,ht⟩
    rw [unitGammaHeadFamilyMap_value] at ht
    have h1 : a.val.1 = u := congrArg Prod.fst ha
    have h2 : a.val.2 = γ := congrArg Prod.snd ha
    rw [h1,h2] at ht
    exact ht
  · intro ht
    refine ⟨⟨(u,γ),Set.mem_univ _⟩,rfl,?_⟩
    rwa [unitGammaHeadFamilyMap_value]

theorem rvGammaReverseLift_head
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) p).prod ((volumeGammaSpace hc).power (Fin (n+1))))) :
    (rvGammaReverseLift T).carrier = (unaryGammaFamilyLift (rvGammaHeadFamily T)).carrier := by
  ext u
  change (u ∘ Fin.castAdd (n+1), rvUnitTupleValues (u ∘ Fin.natAdd p ∘ Fin.rev)) ∈ T.carrier ↔
    (Fin.init u,rvUnitValueHom (u (Fin.last (p+n)))) ∈ (rvGammaHeadFamily T).carrier
  symm
  refine (rvGammaHeadFamily_mem T (Fin.init u) _).trans ?_
  have hbase : Fin.init u ∘ Fin.castAdd n = u ∘ Fin.castAdd (n+1) := by
    funext j
    apply congrArg u
    apply Fin.ext
    rfl
  have hvalues : Fin.cons (rvUnitValueHom (u (Fin.last (p+n))))
      (rvUnitTupleValues (Fin.init u ∘ Fin.natAdd p ∘ Fin.rev)) =
      rvUnitTupleValues (u ∘ Fin.natAdd p ∘ Fin.rev) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero, Fin.rev_zero, Function.comp_def, rvUnitTupleValues]
      apply congrArg (fun k => rvUnitValueHom (u k))
      apply Fin.ext
      simp only [Fin.val_natAdd,Fin.val_last]
    · simp only [Fin.cons_succ, Fin.rev_succ, Function.comp_def, rvUnitTupleValues,Fin.init]
      apply congrArg (fun k => rvUnitValueHom (u k))
      apply Fin.ext
      rfl
  rw [hbase,hvalues]

end DiamondIntegral.Section5
