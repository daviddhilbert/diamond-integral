import «section 5».NativeVFBaseTransport
import «section 5».NativeSpecialBaseBridge
import «section 5».PreparedMixedCoordinates

/-! Transporting all VF coordinates leaves every old RV parameter and
has the exact inverse-source normal form. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n r l : ℕ}
variable (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r))
variable {P : GammaGroundDefSet hc B (rawMixedSpace (M := M) n 0)}
variable {C : GammaGroundDefSet hc B (rawMixedSpace (M := M) n l)} (T : GammaGroundBijection P C)
variable (hP : ∀ a : A,((nativeMixedCoordinateMap A (Fin.castAdd 0) (Fin.elim0 : Fin 0 → Fin r)) a).val ∈ P.carrier)

theorem nativeVFPrepareAll_value (a : A) :
    ((nativeVFPrepareBaseMap (k := 0) A T hP) a).val =
      ((T.map ((nativeVFBaseParameterMap (k := 0) A P hP) a)).val.1,
        Fin.append (T.map ((nativeVFBaseParameterMap (k := 0) A P hP) a)).val.2 a.val.2) := by
  let d := T.map ((nativeVFBaseParameterMap (k := 0) A P hP) a)
  have hx : Fin.append d.val.1 (a.val.1 ∘ (Fin.natAdd n : Fin 0 → Fin n)) = d.val.1 :=
    funext (fun i => Fin.append_left _ _ i)
  have hh : (Fin.append d.val.1 (a.val.1 ∘ (Fin.natAdd n : Fin 0 → Fin n)),Fin.append d.val.2 a.val.2) =
      (d.val.1,Fin.append d.val.2 a.val.2) :=
    congrArg (fun x : Fin n → Section2.VF M => (x,Fin.append d.val.2 a.val.2)) hx
  exact (nativeVFPrepareBaseMap_value (k := 0) A T hP a).trans hh

theorem nativeVFPrepareAll_normalForm (c : C) (u : Fin r → CanonicalRV.RVSort M) :
    (c.val.1,Fin.append c.val.2 u) ∈ (nativeVFPrepareBaseMap (k := 0) A T hP).image.carrier ↔
      ((T.symm.map c).val.1,u) ∈ A.carrier := by
  constructor
  · rintro ⟨a,ha⟩
    let b := (nativeVFBaseParameterMap (k := 0) A P hP) a
    let d := T.map b
    have hpack : (d.val.1,Fin.append d.val.2 a.val.2) = (c.val.1,Fin.append c.val.2 u) :=
      (nativeVFPrepareAll_value A T hP a).symm.trans ha
    have hdVF : d.val.1 = c.val.1 := congrArg (fun z : Section2.Mixed M n (l+r) => z.1) hpack
    have hdRV : d.val.2 = c.val.2 := funext (fun i => by
      simpa only [Fin.append_left] using congrArg (fun w : Section2.Mixed M n (l+r) => w.2 (Fin.castAdd r i)) hpack)
    have hd : d = c := Subtype.ext (Prod.ext hdVF hdRV)
    have hb : b = T.symm.map c := T.bijective.1 (hd.trans (T.map.apply_inverse T.bijective c).symm)
    have hx : a.val.1 = (T.symm.map c).val.1 := by
      have h := congrArg (fun z : P => z.val.1) hb
      exact h
    have hu : a.val.2 = u := funext (fun i => by
      simpa only [Fin.append_right] using congrArg (fun w : Section2.Mixed M n (l+r) => w.2 (Fin.natAdd l i)) hpack)
    exact (congrArg₂ Prod.mk hx hu) ▸ a.property
  · intro ha
    let a : A := ⟨((T.symm.map c).val.1,u),ha⟩
    have hb : (nativeVFBaseParameterMap (k := 0) A P hP) a = T.symm.map c := by
      apply Subtype.ext
      exact Prod.ext rfl (Subsingleton.elim _ _)
    refine ⟨a,?_⟩
    change ((nativeVFPrepareBaseMap (k := 0) A T hP) a).val = _
    exact (nativeVFPrepareAll_value A T hP a).trans (by
      have he : T.map ((nativeVFBaseParameterMap (k := 0) A P hP) a) = c :=
        (congrArg T.map hb).trans (T.map.apply_inverse T.bijective c)
      exact congrArg (fun d : C => (d.val.1,Fin.append d.val.2 u)) he)

theorem nativeVFPrepareAll_base_mem (w : Section2.Mixed M n (l+r))
    (hw : w ∈ (nativeVFPrepareBaseMap (k := 0) A T hP).image.carrier) :
    (w.1,w.2 ∘ Fin.castAdd r) ∈ C.carrier := by
  obtain ⟨a,ha⟩ := hw
  let d := T.map ((nativeVFBaseParameterMap (k := 0) A P hP) a)
  have he : (d.val.1,Fin.append d.val.2 a.val.2) = w :=
    (nativeVFPrepareAll_value A T hP a).symm.trans ha
  have hh : (w.1,w.2 ∘ Fin.castAdd r) = d.val := by
    apply Prod.ext
    · exact (congrArg (fun z : Section2.Mixed M n (l+r) => z.1) he).symm
    · funext i
      have hi := congrArg (fun z : Section2.Mixed M n (l+r) => z.2 (Fin.castAdd r i)) he
      simpa only [Function.comp_apply,Fin.append_left] using hi.symm
  exact hh.symm ▸ d.property

theorem nativeVFPrepareAll_pullback (hpull : IsRVPullback C.carrier)
    (Q : (Fin (n+l) → CanonicalRV.RVSort M) → (Fin r → CanonicalRV.RVSort M) → Prop)
    (hrow : ∀ (c : C) (u : Fin r → CanonicalRV.RVSort M),
      ((T.symm.map c).val.1,u) ∈ A.carrier ↔ Q (flatKey c.val).2 u) :
    IsRVPullback (nativeVFPrepareBaseMap (k := 0) A T hP).image.carrier := by
  apply (isRVPullback_iff _).mpr
  intro w hw w' hsame
  have hr := (sameRV_iff w w').mp hsame
  have hb := nativeVFPrepareAll_base_mem A T hP w hw
  let c : C := ⟨(w.1,w.2 ∘ Fin.castAdd r),hb⟩
  have hsbase : SameRV c.val (w'.1,w'.2 ∘ Fin.castAdd r) :=
    (sameRV_iff _ _).mpr ⟨hr.1,congrArg (fun t => t ∘ Fin.castAdd r) hr.2⟩
  let c' : C := ⟨(w'.1,w'.2 ∘ Fin.castAdd r),(mem_iff_sameRV hpull hsbase).mp c.property⟩
  have hk : (flatKey c.val).2 = (flatKey c'.val).2 :=
    congrArg Prod.snd ((flatKey_eq_iff _ _).mpr hsbase)
  have hu : w.2 ∘ Fin.natAdd l = w'.2 ∘ Fin.natAdd l :=
    congrArg (fun t => t ∘ Fin.natAdd l) hr.2
  have hpack : (c.val.1,Fin.append c.val.2 (w.2 ∘ Fin.natAdd l)) = w :=
    Prod.ext rfl Fin.append_castAdd_natAdd
  have hpack' : (c'.val.1,Fin.append c'.val.2 (w'.2 ∘ Fin.natAdd l)) = w' :=
    Prod.ext rfl Fin.append_castAdd_natAdd
  have hq : Q (flatKey c.val).2 (w.2 ∘ Fin.natAdd l) :=
    (hrow c _).mp ((nativeVFPrepareAll_normalForm A T hP c _).mp (hpack.symm ▸ hw))
  have hq' : Q (flatKey c'.val).2 (w'.2 ∘ Fin.natAdd l) :=
    (congrArg₂ Q hk hu).mp hq
  exact hpack' ▸ (nativeVFPrepareAll_normalForm A T hP c' _).mpr ((hrow c' _).mpr hq')

end DiamondIntegral.Section5
