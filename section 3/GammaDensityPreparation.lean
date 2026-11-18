import «section 3».GammaDensityCodeRows
import «section 3».GammaPreparedBaseJacobian
import «section 5».NativeArbitraryVFPullbackPreparation

/-! Simultaneous preparation of a VF domain and the complete graph of
its Gamma density. The resulting density is constant on each entire RV
polydisc; every preparation map retains the original Gamma ground. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.Section4.rawMixedSpace SpecialTransformations.Section4.rawVFSpace
  SpecialTransformations.Section4.rawRVSpace SpecialTransformations.Section4.realSpace
  SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section9
open IntegrationInACVF.Section6
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaDensity_preparation
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r))
    (ω : GammaGroundVolumeForm hc B A) :
    ∃ l : ℕ, ∃ Y : GammaGroundDefSet hc B (rawMixedSpace (M := M) n (l+r)),
      ∃ e : GammaGroundBijection A Y, SpecialTransformations.Section5.IsRVPullback Y.carrier ∧
        (∀ a, AlgebraicIndependent (vfParameterField B.real) a.val.1 → HasMixedVFJacobianAt e.map a 1) ∧
        ∀ a b : A, Section5.nativeMixedFullKeyMap Y (e.map a) = Section5.nativeMixedFullKeyMap Y (e.map b) →
          (ω a).val = (ω b).val := by
  let lengths : Bool → ℕ := fun i => if i then r+1 else r
  let D : (i : Bool) → GammaDomainFormula B n (lengths i) (fun _ => .vf)
    | false => ⟨Section5.nativeMixedDomain A,Section5.nativeMixedDomain_definable A⟩
    | true => ⟨gammaDensityCodeRows ω,gammaDensityCodeRows_definable ω⟩
  let P : SpecialTransformations.Section5.DefSet (M := M) B.real n 0 :=
    SpecialTransformations.Section5.PresentedSet.univ (SpecialTransformations.Section5.pointSpace n 0) B.real
  have hP : SpecialTransformations.Section5.GammaSetDefinable B (SpecialTransformations.Section5.carrier P) :=
    (SpecialTransformations.Section5.gammaLogicInput B).real_set _ (SpecialTransformations.Section5.setDefinable P)
  obtain ⟨R,hPR,hBR,l,C,T,hT,hC,hrows⟩ := Section5.prepare_finite_original_base_RV_predicates
    hκ hs h00 B hr P hP lengths D
  let TΓ := Section5.nativeSpecialBaseBijection (hc := hc) T hT
  have hPA : ∀ a : A,((Section5.nativeMixedCoordinateMap A (Fin.castAdd 0) (Fin.elim0 : Fin 0 → Fin r)) a).val ∈
      (Section5.nativeGammaPointDomain (hc := hc)
        (SpecialTransformations.Section5.carrier (SpecialTransformations.Section5.extendBase P hPR))
        (SpecialTransformations.Section5.GammaChainDefinable.source B T.chain hT)).carrier := fun _ => Set.mem_univ _
  let Y := (Section5.nativeVFPrepareBaseMap (k := 0) A TΓ hPA).image
  let e := Section5.nativeVFPrepareBaseBijection (k := 0) A TΓ hPA
  let b := Section5.nativeVFBaseParameterMap (k := 0) A _ hPA
  have he (a : A) : (e.map a).val =
      ((T.toMap (b a)).val.1,Fin.append (T.toMap (b a)).val.2 a.val.2) := by
    have hh := Section5.nativeVFPrepareAll_value A TΓ hPA a
    have ht := Section5.nativeGammaPointBijection_apply
      (SpecialTransformations.Section5.GammaChainDefinable.source B T.chain hT)
      (SpecialTransformations.Section5.GammaChainDefinable.target B T.chain hT)
      (Section5.nativeSpecialBaseIso T hT) (b a)
    exact hh.trans (congrArg (fun z => (z.1,Fin.append z.2 a.val.2)) ht)
  refine ⟨l,Y,e,?_,gammaPreparedBase_jacobian_one hκ.le hs hr hv A T hT hPA,?_⟩
  · apply Section5.nativeVFPrepareAll_pullback A TΓ hPA hC
      (fun t u => Fin.append (rvValues t) (rvValues u) ∈ ((GammaParameterRecode.prepared T hT).domain (D false)).val)
    intro c u
    have hcode := Section5.nativeSpecialBaseBijection_parameter T hT c u
    have hmem := (Section5.nativeMixedCode_mem_domain_iff A ((TΓ.symm.map c).val.1,u)).symm
    have hh : Section5.nativeMixedCode ((TΓ.symm.map c).val.1,u) ∈ (D false).val ↔
        Fin.append (rawVFParameter (T.inverseMap ⟨c.val,c.property⟩).val) (rvValues u) ∈ (D false).val :=
      (congrArg (fun w => w ∈ (D false).val) hcode).to_iff
    exact hmem.trans (hh.trans (hrows false ⟨c.val,c.property⟩ (rvValues u)))
  · intro a a' hkey
    have hflat : SpecialTransformations.Section5.flatKey (e.map a).val =
        SpecialTransformations.Section5.flatKey (e.map a').val :=
      Prod.ext (Subsingleton.elim _ _) (congrArg Subtype.val hkey)
    have hsame := (SpecialTransformations.Section5.sameRV_iff _ _).mp
      ((SpecialTransformations.Section5.flatKey_eq_iff _ _).mp hflat)
    have hlabels : Fin.append (T.toMap (b a)).val.2 a.val.2 =
        Fin.append (T.toMap (b a')).val.2 a'.val.2 := by simpa only [he] using hsame.2
    have hold : a.val.2 = a'.val.2 := by
      simpa only [Function.comp_def,Fin.append_right] using
        congrArg (fun v : Fin (l+r) → CanonicalRV.RVSort M => v ∘ Fin.natAdd l) hlabels
    have hnew : (T.toMap (b a)).val.2 = (T.toMap (b a')).val.2 := by
      simpa only [Function.comp_def,Fin.append_left] using
        congrArg (fun v : Fin (l+r) → CanonicalRV.RVSort M => v ∘ Fin.castAdd r) hlabels
    have hbase : SpecialTransformations.Section5.SameRV (T.toMap (b a)).val (T.toMap (b a')).val :=
      (SpecialTransformations.Section5.sameRV_iff _ _).mpr ⟨by simpa only [he,Nat.add_zero] using hsame.1,hnew⟩
    have hk : rawPreparedKey (T.toMap (b a)).val = rawPreparedKey (T.toMap (b a')).val :=
      congrArg (fun z : SpecialTransformations.Section5.Point (M := M) 0 (n+l) => rvValues z.2) ((SpecialTransformations.Section5.flatKey_eq_iff _ _).mpr hbase)
    obtain ⟨c,hcω⟩ := (volumeGammaSpace hc).onto (ω a).val
    have ha := (gammaDensityCodeRows_mem ω a.val c).mpr ⟨a,rfl,hcω.symm⟩
    have hrowA := hrows true (T.toMap (b a)) (Fin.append (rvValues a.val.2) c.val)
    have hrowB := hrows true (T.toMap (b a')) (Fin.append (rvValues a'.val.2) c.val)
    simp only [SpecialTransformations.Section5.SpecialBijection.inverse_apply] at hrowA hrowB
    have hshared := hrowA.mp ha
    rw [hk,hold] at hshared
    have hb := hrowB.mpr hshared
    obtain ⟨t,ht,hw⟩ := (gammaDensityCodeRows_mem ω a'.val c).mp hb
    have ht' : t = a' := Subtype.ext ht
    exact hcω.symm.trans ((congrArg (fun z : A => (ω z).val) ht').symm.trans hw).symm

end DiamondIntegral.Section3
