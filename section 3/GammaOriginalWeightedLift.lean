import «section 3».GammaOriginalLiftGraphs
import Section9.WeightedLiftJacobian

/-! The weighted Jacobian lift over the original real/Gamma base. The
finite-volume correspondence and its polynomial lift retain that base;
no real representative of a Gamma parameter is named. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open SpecialTransformations.Section7 SpecialTransformations.Section9
open scoped BigOperators

namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n : ℕ}

theorem gammaOriginalLift_same_labels (U : GammaRVObject B n) (p q : U.lift)
    (h : p.val.2 = q.val.2) :
    (fun i => rv (p.val.1 i)) = fun i => rv (q.val.1 i) := by
  obtain ⟨u,hu,hvu⟩ := volume_of_lift U p
  obtain ⟨v,hv,hvv⟩ := volume_of_lift U q
  have he : u = v := Subtype.ext (hu.trans (h.trans hv.symm))
  exact hvu.symm.trans (he ▸ hvv)

theorem gammaOriginalWeightedLift [CharZero (Section2.VF M)]
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    (hB : VFGammaGeneratedBase B)
    {G : Type} [LinearOrderedCommGroupWithZero G] (w : Valuation (Section2.VF M) G)
    (hw : ∀ x y : Section2.VF M, VFValued.predV x y ↔ w x ≤ w y)
    {U V : GammaRVObject B n} (e : GammaRVIso U V)
    (hU : ∀ u : rvObjectDomain U.object, ∀ i, (gammaVolumeValue U u i).val ≠ iRVZero)
    (hV : ∀ v : rvObjectDomain V.object, ∀ i, (gammaVolumeValue V v i).val ≠ iRVZero) :
    ∃ f : GammaIso B U.lift V.lift,
      (∀ p : U.lift, ∃ u : rvObjectDomain U.object,
        u.val = p.val.2 ∧ (e.equiv u).val = (f.equiv p).val.2) ∧
      ∀ p : U.lift, AlgebraicIndependent (vfParameterField B.real) p.val.1 →
        ∃ J : Section2.VF M, HasMixedVFJacobianAt f.equiv p J ∧
          w J = (∏ i, w ((f.equiv p).val.1 i)) / ∏ i, w (p.val.1 i) := by
  let C := gammaRawVolumeCorrespondence U V e.equiv
  have hC : ∀ z ∈ C, ∀ i, z i ≠ iRVZero := by
    rintro z ⟨u,rfl⟩ i
    obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective i
    cases j with
    | inl j =>
      change productTuple _ _ (productLeft n n j) ≠ iRVZero
      rw [productTuple_left]
      exact hU u j
    | inr j =>
      change productTuple _ _ (productRight n n j) ≠ iRVZero
      rw [productTuple_right]
      exact hV (e.equiv u) j
  obtain ⟨A,hA,hGood,hWeighted⟩ := exists_lift_with_weighted_blocks w hw hκ hs h00 B hsmall hB
    C (gammaRawVolumeCorrespondence_definable U V e.equiv e.graph) hC e.leftFinite e.rightFinite
  obtain ⟨f,hGraph⟩ := gammaOriginalLiftIso_with_graph e.equiv A hGood
    (gammaLiftGraph_definable hc e A hA)
  refine ⟨f,fun p => (hGraph p).2.2.1,?_⟩
  intro p hp
  let a := p.val.1
  let b := (f.equiv p).val.1
  let r (x : Fin n → Section2.VF M) : Fin n → _root_.RVCalc.RV w :=
    fun i => _root_.RVCalc.rv w (x i)
  let t := r a
  let s := r b
  have hcode (x : Fin n → Section2.VF M) :
      rawRV w hw (r x) = fun i => (rv (x i)).val := by
    funext i
    exact congrArg Subtype.val (CanonicalRV.equiv_rv w hw (x i))
  have hpair : productTuple (rawRV w hw t) (rawRV w hw s) ∈ C := by
    obtain ⟨u,hu,htu⟩ := volume_of_lift U p
    obtain ⟨v,hv,hsv⟩ := volume_of_lift V (f.equiv p)
    obtain ⟨u',hu',hv'⟩ := (hGraph p).2.2.1
    have heu : u' = u := Subtype.ext (hu'.trans hu.symm)
    have hev : e.equiv u' = v := Subtype.ext (hv'.trans hv.symm)
    have htu' : (fun i => (gammaVolumeValue U u i).val) =
        fun i => (rv (a i)).val := congrArg (fun z => fun i => (z i).val) htu
    have hsv' : (fun i => (gammaVolumeValue V v i).val) =
        fun i => (rv (b i)).val := congrArg (fun z => fun i => (z i).val) hsv
    change productTuple (rawRV w hw (r a)) (rawRV w hw (r b)) ∈ C
    rw [hcode,hcode,←htu',←hsv',←hev,←heu]
    exact ⟨u',rfl⟩
  obtain ⟨H,hH⟩ := hWeighted t s hpair
  let E := vfDefinableClosureFieldBase B
  let P : Fin n → MvPolynomial (Fin (n+n)) (Section2.VF M) := fun i => (H i).map E.subtype
  letI : Valued (Section2.VF M) G := Valued.mk' w
  obtain ⟨L,F,hChart,hL⟩ := gammaOriginalIso_differentiable hc hκ hs hsmall hw
    U.lift_definable V.lift_definable f p hp
  have hCenter : F a = b := hChart.center
  obtain ⟨ρ,hρ⟩ := hChart
  have hFibre (x y : Fin n → Section2.VF M)
      (h : (fun i => rv (x i)) = fun i => rv (y i)) : x ∈ RVFibre w (r y) := by
    intro i
    apply (CanonicalRV.equiv w hw).injective
    rw [CanonicalRV.equiv_rv,CanonicalRV.equiv_rv]
    exact congrFun h i
  have hLocal (x : Fin n → Section2.VF M) (hx : x ∈ vfBall a ρ) :
      x ∈ RVFibre w t ∧ F x ∈ RVFibre w s ∧ productTuple (rawVF x) (rawVF (F x)) ∈ A := by
    obtain ⟨hxU,he⟩ := hρ x hx
    let q : U.lift := ⟨(x,p.val.2),hxU⟩
    have hq : (f.equiv q).val = (F x,(f.equiv p).val.2) := he
    have hqx := gammaOriginalLift_same_labels U q p rfl
    have hqy : (fun i => rv (F x i)) = fun i => rv (b i) := by
      have htag := congrArg (fun z : Point (M := M) n (rvObjectArity V.object) => z.2) hq
      have ht := gammaOriginalLift_same_labels V (f.equiv q) (f.equiv p) htag
      have hfibre := congrArg (fun z : Point (M := M) n (rvObjectArity V.object) =>
        fun i => rv (z.1 i)) hq
      exact hfibre.symm.trans ht
    refine ⟨hFibre x a hqx,hFibre (F x) b hqy,?_⟩
    have ht := (hGraph q).2.2.2
    rw [hq] at ht
    exact ht
  have heq : ∀ x ∈ vfBall a ρ, ∀ i, (P i).eval (productTuple x (F x)) = 0 := by
    intro x hx
    obtain ⟨hxt,hxs,hxa⟩ := hLocal x hx
    exact (hH x hxt (F x) hxs).1.mp hxa
  obtain ⟨hat,has,haA⟩ := hLocal a (mem_vfBall_self a ρ)
  have hblocks := (hH a hat (F a) has).2 haA
  have ha0 (i : Fin n) : a i ≠ 0 := by
    obtain ⟨u,_,hu⟩ := volume_of_lift U p
    intro hi
    have he := congrArg Subtype.val (congrFun hu i)
    change (gammaVolumeValue U u i).val = (CanonicalRV.encodedRv (a i)).val at he
    rw [hi] at he
    exact hU u i (he.trans (RVCalc.rv_zero_eq hM))
  refine ⟨(LinearMap.toMatrix' L).det,⟨F,⟨ρ,hρ⟩,hL.hasJacobianAt⟩,?_⟩
  exact (vfJacobian_value_of_blocks w P F a L hL ρ heq ha0 hblocks).trans
    (congrArg (fun y : Fin n → Section2.VF M =>
      (∏ i,w (y i)) / ∏ i,w (a i)) hCenter)

end DiamondIntegral.Section3
