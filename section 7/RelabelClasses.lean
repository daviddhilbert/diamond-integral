import «section 7».FirstStage
import Section4.RVReindexing

/-! Head-start objects over relabelled RV targets (for Lemma 7.21).

`FirstStage.cls_labelObject_eq` compares two head-start objects over the same
RV target. The two standard contractions of a `2`-cell in the orders `12` and
`21` end on RV targets whose label coordinates differ by a permutation `τ` (the
labels of the two stages come in the opposite order). `cls_labelObject_relabel`
compares head-start objects over targets `U`, `U'` with `u ∈ U ↔ u ∘ τ ∈ U'`,
whose volume labels agree through `τ` up to order and whose forms agree through
`τ`: then the classes are equal. The isomorphism is `u ↦ u ∘ τ`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.RelabelClasses
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.ChartOfMeasured
open DiamondIntegral.Section7.FiberwiseInput DiamondIntegral.Section7.FirstStage

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) {T : LRV.Substructure M}
variable {a b qX qY kX kY : ℕ}
variable {X : DefSet (rawMixedSpace (M := M) a qX) (T : Set M)} {Y : DefSet (rawMixedSpace (M := M) b qY) (T : Set M)}
variable {U : DefSet (rawMixedSpace (M := M) 0 qX) (T : Set M)} {U' : DefSet (rawMixedSpace (M := M) 0 qY) (T : Set M)}
variable {νX : Fin a → Fin qX} {νY : Fin b → Fin qY}

/-- **Relabelled head-start objects.** Head-start objects over RV targets that
correspond under a permutation `τ` of label coordinates, with volume labels and
forms matching through `τ`, have the same class. -/
theorem cls_labelObject_relabel (h : a + kX = b + kY)
    (hX : ∀ p : Mixed M a qX, p ∈ X.carrier ↔ (Fin.elim0, p.2) ∈ U.carrier ∧ ∀ i, rv M (p.1 i) = p.2 (νX i))
    (hY : ∀ p : Mixed M b qY, p ∈ Y.carrier ↔ (Fin.elim0, p.2) ∈ U'.carrier ∧ ∀ i, rv M (p.1 i) = p.2 (νY i))
    (lX : Fin kX → Fin qX) (lY : Fin kY → Fin qY) (τ : Fin qY ≃ Fin qX)
    (hU : ∀ u : Fin qX → RVInfinity M, (Fin.elim0, u) ∈ U.carrier ↔ (Fin.elim0, u ∘ τ) ∈ U'.carrier)
    (hprod : ∀ f : Fin qX → Gamma M, ∏ i, f (Fin.append νX lX i) = ∏ i, f (τ (Fin.append νY lY i)))
    (ρ : Map U (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M)))
    (ρ' : Map U' (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M)))
    (hρ : ∀ (z : U) (z' : U'), z'.val.2 = z.val.2 ∘ τ → (ρ z).val = (ρ' z').val)
    (hTX : ∀ p ∈ X.carrier, ∀ z ∈ X.carrier, p.2 = z.2 → tupleRV M p.1 = tupleRV M z.1)
    (hTY : ∀ p ∈ Y.carrier, ∀ z ∈ Y.carrier, p.2 = z.2 → tupleRV M p.1 = tupleRV M z.1)
    (hfinX hfinY hnzX hnzY)
    (ηX : Map X (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M))) (hηX)
    (ηY : Map Y (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M))) (hηY)
    (hρX : ∀ (p : X) (z : U), z.val.2 = p.val.2 → (ηX p).val = (ρ z).val)
    (hρY : ∀ (p : Y) (z : U'), z.val.2 = p.val.2 → (ηY p).val = (ρ' z).val)
    (hdX : (labelObject X kX lX hTX hfinX hnzX ηX hηX).doublyBounded)
    (hdY : (labelObject Y kY lY hTY hfinY hnzY ηY hηY).doublyBounded) :
    cls (objOf hc T (labelObject X kX lX hTX hfinX hnzX ηX hηX) hdX) =
      castCls h.symm (cls (objOf hc T (labelObject Y kY lY hTY hfinY hnzY ηY hηY) hdY)) := by
  have hmem : ∀ u : (preparedHeadStartRVObject X kX lX hTX).domain,
      u.val ∘ τ ∈ (preparedHeadStartRVObject Y kY lY hTY).domain.carrier := fun u =>
    (mem_domain_labels hY lY hTY _).mpr ((hU u.val).mp ((mem_domain_labels hX lX hTX u.val).mp u.property))
  let F : Map (preparedHeadStartRVObject X kX lX hTX).domain (preparedHeadStartRVObject Y kY lY hTY).domain :=
    ((rvReindexMap (T : Set M) τ).comp (Map.inclusion (fun _ _ => Set.mem_univ _))).corestrict hmem
  have hF_val (u : (preparedHeadStartRVObject X kX lX hTX).domain) : (F u).val = u.val ∘ τ := rfl
  have hF : Function.Bijective F := by
    refine ⟨fun x y he => ?_, fun v => ?_⟩
    · have h1 : x.val ∘ τ = y.val ∘ τ := by rw [← hF_val, ← hF_val, he]
      apply Subtype.ext
      funext i
      have := congrFun h1 (τ.symm i)
      simpa only [Function.comp_apply, Equiv.apply_symm_apply] using this
    · have hv : v.val ∘ τ.symm ∈ (preparedHeadStartRVObject X kX lX hTX).domain.carrier := by
        refine (mem_domain_labels hX lX hTX _).mpr ((hU _).mpr ?_)
        have he : v.val ∘ τ.symm ∘ τ = v.val := by
          funext i; simp only [Function.comp_apply, Equiv.symm_apply_apply]
        rw [show (v.val ∘ τ.symm) ∘ τ = v.val from he]
        exact (mem_domain_labels hY lY hTY v.val).mp v.property
      refine ⟨⟨_, hv⟩, Subtype.ext ?_⟩
      rw [hF_val]
      funext i
      simp only [Function.comp_apply, Equiv.symm_apply_apply]
  refine cls_eq_of_volume hc h hdX hdY F hF (fun u => ?_) (fun u => ?_)
  · rw [volumeGamma_eq, volumeGamma_eq]
    change ∏ i, gam ((preparedHeadStartRVObject X kX lX hTX).value u i) =
      ∏ i, gam ((preparedHeadStartRVObject Y kY lY hTY).value (F u) i)
    rw [value_labels hX lX hTX, value_labels hY lY hTY]
    simp only [hF_val, Function.comp_apply]
    exact hprod (fun l => gam (u.val l))
  · obtain ⟨p, rfl⟩ := pureRVTagQuotient_surjective _ u
    obtain ⟨p', hp'⟩ := pureRVTagQuotient_surjective _ (F (pureRVTagQuotient _ p))
    have hpp : p'.val.2 = p.val.2 ∘ τ := congrArg Subtype.val hp'
    have hUp : (Fin.elim0, p.val.2) ∈ U.carrier := ((mem_bundle_labels hX lX p.val).mp p.property).1
    have hUp' : (Fin.elim0, p'.val.2) ∈ U'.carrier := ((mem_bundle_labels hY lY p'.val).mp p'.property).1
    let z : U := ⟨(Fin.elim0, p.val.2), hUp⟩
    let z' : U' := ⟨(Fin.elim0, p'.val.2), hUp'⟩
    change (headStartRVForm X kX lX ηX hηX (pureRVTagQuotient _ p)).val =
      (headStartRVForm Y kY lY ηY hηY (F (pureRVTagQuotient _ p))).val
    rw [← hp', headStartRVForm_at, headStartRVForm_at]
    refine (hρX _ z ?_).trans ((hρ z z' hpp).trans (hρY _ z' ?_).symm)
    · rw [headStartBaseProjection_value]
    · rw [headStartBaseProjection_value]

end DiamondIntegral.Section7.RelabelClasses
