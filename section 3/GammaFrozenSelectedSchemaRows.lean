import «section 3».GammaFrozenParameterRecoding
import «section 3».GammaFrozenSelectedHeadRows

/-! Selected-family rows specialize literally when only the VF tail is
frozen. Gamma-code row agreement suffices for the existing formula
machinery, without choosing an RV-valued density function. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

theorem gammaMeasured_rowAgreement_of_typed_codes
    {p q a k : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}
    (F : GammaMeasuredRVSchema hc B p a (k+1) sp) (z : Fin p → M)
    (E : GammaMeasuredRVSchema hc B q a (k+1) sq) (t : Fin q → M)
    (hV : GammaSchemaRowAgreement F.object z E.object t)
    (hD : ∀ (r : Fin a → RV (M := M)) (c : (volumeGammaSpace hc).domain), F.rowDensity z r c ↔ E.rowDensity t r c) :
    GammaVolumeRowAgreement F.toRVTemplate z E.toRVTemplate t := by
  apply gammaVolumeRowAgreement_of_typed F.toRVTemplate z E.toRVTemplate t hV
  intro r w
  constructor
  · intro hd
    have hCode : rvValues w ∈ (volumeGammaSpace hc).domain := by
      simpa only [Function.comp_def,Fin.append_right] using F.density_code _ hd
    exact (hD r ⟨rvValues w,hCode⟩).mp hd
  · intro hd
    have hCode : rvValues w ∈ (volumeGammaSpace hc).domain := by
      simpa only [Function.comp_def,Fin.append_right] using E.density_code _ hd
    exact (hD r ⟨rvValues w,hCode⟩).mpr hd

variable {n a k : ℕ} {U : DefSet (M := M) Set.univ (n+1) a}
variable (hU : GammaSetDefinable B (carrier U)) (ρ : Fin (k+1) → Fin a)
variable (Q : GammaGroundDefSet hc B (rawRVSpace (M := M) a))
variable (hLabels : ∀ u : U, u.val.2 ∈ Q.carrier) (ω : GammaGroundVolumeForm hc B Q)
variable (x : Fin n → VF (M := M))

def gammaFrozenRetainedForm :=
  gammaPointRetainedForm (extendBase (coordinateFibre U 0 (headFrozenTuple x)) (Set.subset_univ _))
    (gammaFrozenHeadPreparation_source hU x)
    (Q.monoReal (T := B.real ∪ Set.range (vfValues x)) Set.subset_union_left) id
    (fun p => gammaFrozenHeadLabels (hc := hc) (x := x) hU Q hLabels p)
    (ω.monoReal (T := B.real ∪ Set.range (vfValues x)) Set.subset_union_left)

theorem gammaFrozenSelectedSchema_rowAgreement (N L : ℕ) (z : Fin 1 → VF (M := M)) :
    let F := gammaMeasuredSchemaChangeBase (gammaFrozenFormulaBaseChange B x)
      (gammaMeasuredBoundedSelectedSchema U hU ρ (gammaPointRetainedForm U hU Q id (fun p => hLabels p) ω) N)
    let E := gammaMeasuredBoundedSelectedSchema
      (extendBase (coordinateFibre U 0 (headFrozenTuple x)) (Set.subset_univ _))
      (gammaFrozenHeadPreparation_source hU x) ρ (gammaFrozenRetainedForm hU Q hLabels ω x) L
    GammaVolumeRowAgreement F.toRVTemplate (vfValues (Fin.cons (z 0) x)) E.toRVTemplate (vfValues z) := by
  intro F E
  apply gammaMeasured_rowAgreement_of_typed_codes F _ E _
  · apply gammaSchemaRowAgreement_of_typed F.object _ E.object _
    · intro r
      have hF := gammaSelectedLabelSchema_domain U hU ρ (Fin.cons (z 0) x)
      have hE := gammaSelectedLabelSchema_domain
        (extendBase (coordinateFibre U 0 (headFrozenTuple x)) (Set.subset_univ _)) (gammaFrozenHeadPreparation_source hU x) ρ z
      change r ∈ (gammaSelectedLabelSchema U hU ρ).rowDomain (vfValues (Fin.cons (z 0) x)) ↔
        r ∈ (gammaSelectedLabelSchema (extendBase (coordinateFibre U 0 (headFrozenTuple x)) (Set.subset_univ _))
          (gammaFrozenHeadPreparation_source hU x) ρ).rowDomain (vfValues z)
      have hMem : (Fin.cons (z 0) x,r) ∈ carrier U ↔
          (z,r) ∈ carrier (extendBase (coordinateFibre U 0 (headFrozenTuple x)) (Set.subset_univ _)) := by
        change (Fin.cons (z 0) x,r) ∈ carrier U ↔ coordinateInsert 0 (headFrozenTuple x) (z,r) ∈ carrier U
        rw [coordinateInsert_head]
        rfl
      exact (Set.ext_iff.mp hF r).trans (hMem.trans (Set.ext_iff.mp hE r).symm)
    · intro r y
      have hF := gammaSelectedLabelSchema_volume U hU ρ (Fin.cons (z 0) x) r y
      have hE := gammaSelectedLabelSchema_volume
        (extendBase (coordinateFibre U 0 (headFrozenTuple x)) (Set.subset_univ _)) (gammaFrozenHeadPreparation_source hU x) ρ z r y
      apply hF.trans
      apply Iff.trans ?_ hE.symm
      change ((Fin.cons (z 0) x,r) ∈ carrier U ∧ _) ↔ (coordinateInsert 0 (headFrozenTuple x) (z,r) ∈ carrier U ∧ _)
      rw [coordinateInsert_head]
      rfl
  · intro r c
    let Ω := gammaPointRetainedForm U hU Q id (fun p => hLabels p) ω
    let Ux := extendBase (coordinateFibre U 0 (headFrozenTuple x)) (Set.subset_univ _)
    let hUx := gammaFrozenHeadPreparation_source hU x
    let Ωx := gammaFrozenRetainedForm hU Q hLabels ω x
    change (gammaMeasuredSelectedSchema U hU ρ Ω).rowDensity (vfValues (Fin.cons (z 0) x)) r c ↔
      (gammaMeasuredSelectedSchema Ux hUx ρ Ωx).rowDensity (vfValues z) r c
    rw [gammaMeasuredSelectedSchema_density,gammaMeasuredSelectedSchema_density]
    constructor
    · rintro ⟨p,hp,hω⟩
      have hMem : coordinateInsert 0 (headFrozenTuple x) (z,r) ∈ carrier U := by
        rw [coordinateInsert_head]
        exact hp ▸ p.property
      let q : Section5.nativeGammaPointDomain (hc := hc) (carrier Ux) hUx := ⟨(z,r),hMem⟩
      have hWeight : (Ω p).val = (Ωx q).val := by
        change (ω ⟨p.val.2,_⟩).val = (ω ⟨r,_⟩).val
        exact congrArg (fun u : Q => (ω u).val) (Subtype.ext (congrArg Prod.snd hp))
      exact ⟨q,rfl,hWeight.symm.trans hω⟩
    · rintro ⟨q,hq,hω⟩
      have hMem : (Fin.cons (z 0) x,r) ∈ carrier U := by
        have h := q.property
        change coordinateInsert 0 (headFrozenTuple x) q.val ∈ carrier U at h
        rw [hq,coordinateInsert_head] at h
        exact h
      let p : Section5.nativeGammaPointDomain (hc := hc) (carrier U) hU := ⟨(Fin.cons (z 0) x,r),hMem⟩
      have hWeight : (Ωx q).val = (Ω p).val := by
        change (ω ⟨q.val.2,_⟩).val = (ω ⟨r,_⟩).val
        exact congrArg (fun u : Q => (ω u).val) (Subtype.ext (congrArg Prod.snd hq))
      exact ⟨p,rfl,hWeight.symm.trans hω⟩

end DiamondIntegral.Section3
