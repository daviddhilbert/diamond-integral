import «section 7».RelabelClasses

/-! Head-start objects over RV targets related by a definable bijection (for
Lemma 7.21).

`cls_labelObject_map` generalizes `RelabelClasses.cls_labelObject_relabel`: two
head-start objects over RV targets `U`, `U'` have the same class when a definable
bijection `Φ : U → U'` matches their volumes (the product of the `Γ`-values at
the volume labels) and their RV forms. In the balanced case of Lemma 7.21, `Φ`
is built from the RV map `ψ` of Lemma 6.38. The isomorphism of objects is `Φ`,
read on the domains through `toMixed0` and `fromMixed0`, which identify
`RV^q` with `VF⁰ × RV^q`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.MapClasses
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.ChartOfMeasured
open DiamondIntegral.Section7.FiberwiseInput DiamondIntegral.Section7.FirstStage

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {q : ℕ}

/-- `RV^q → VF⁰ × RV^q`. -/
def toMixed0 (A : DefSet (rawRVSpace (M := M) q) S) : Map A (DefSet.univ (rawMixedSpace (M := M) 0 q) S) :=
  Map.ofCodes A (fun u => ((Fin.elim0, u) : Mixed M 0 q)) (fun z => Sum.elim Fin.elim0 z)
    (by
      intro i
      cases i with
      | inl i => exact i.elim0
      | inr j => exact Set.DefinableFun.proj LRV)
    (fun c => ⟨⟨Fin.elim0, funext fun i => i.elim0⟩, c.property⟩)
    (fun c => by
      apply mixedValues_injective
      rw [mixedValues_decode]
      funext i
      cases i with
      | inl i => exact i.elim0
      | inr j => exact (congrFun (SpecialTransformations.Section4.rvValues_decode c) j).symm)

theorem toMixed0_val (A : DefSet (rawRVSpace (M := M) q) S) (u : A) :
    (toMixed0 A u).val = ((Fin.elim0, u.val) : Mixed M 0 q) := rfl

/-- `VF⁰ × RV^q → RV^q`. -/
def fromMixed0 (B : DefSet (rawMixedSpace (M := M) 0 q) S) : Map B (DefSet.univ (rawRVSpace (M := M) q) S) :=
  Map.ofCodes B (fun p => p.2) (fun z => z ∘ Sum.inr) (fun _ => Set.DefinableFun.proj LRV)
    (fun c => c.property.2)
    (fun c => by
      apply rvValues_injective
      rw [SpecialTransformations.Section4.rvValues_decode]
      have h := mixedValues_decode c
      funext j
      exact (congrFun h (Sum.inr j)).symm)

theorem fromMixed0_val (B : DefSet (rawMixedSpace (M := M) 0 q) S) (p : B) : (fromMixed0 B p).val = p.val.2 := rfl

section Classes
variable (hc : CanonicalStructure.IsCanonical (M := M)) {T : LRV.Substructure M}
variable {a b qX qY kX kY : ℕ}
variable {X : DefSet (rawMixedSpace (M := M) a qX) (T : Set M)} {Y : DefSet (rawMixedSpace (M := M) b qY) (T : Set M)}
variable {U : DefSet (rawMixedSpace (M := M) 0 qX) (T : Set M)} {U' : DefSet (rawMixedSpace (M := M) 0 qY) (T : Set M)}
variable {νX : Fin a → Fin qX} {νY : Fin b → Fin qY}

omit [M ⊨ Axioms.ACVF] in
theorem mem_of_val {k : ℕ} {Z : DefSet (rawMixedSpace (M := M) 0 k) (T : Set M)} (z : Z) :
    ((Fin.elim0, z.val.2) : Mixed M 0 k) ∈ Z.carrier := by
  have h : ((Fin.elim0, z.val.2) : Mixed M 0 k) = z.val := Prod.ext (Subsingleton.elim (α := Fin 0 → VF M) _ _) rfl
  rw [h]
  exact z.property

/-- **Head-start objects along a bijection of RV targets.** -/
theorem cls_labelObject_map (h : a + kX = b + kY)
    (hX : ∀ p : Mixed M a qX, p ∈ X.carrier ↔ (Fin.elim0, p.2) ∈ U.carrier ∧ ∀ i, rv M (p.1 i) = p.2 (νX i))
    (hY : ∀ p : Mixed M b qY, p ∈ Y.carrier ↔ (Fin.elim0, p.2) ∈ U'.carrier ∧ ∀ i, rv M (p.1 i) = p.2 (νY i))
    (lX : Fin kX → Fin qX) (lY : Fin kY → Fin qY) (Φ : Map U U') (hΦ : Function.Bijective Φ)
    (hprod : ∀ z : U, ∏ i, gam (z.val.2 (Fin.append νX lX i)) = ∏ i, gam ((Φ z).val.2 (Fin.append νY lY i)))
    (ρ : Map U (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M)))
    (ρ' : Map U' (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M)))
    (hρ : ∀ z : U, (ρ z).val = (ρ' (Φ z)).val)
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
  let domX := (preparedHeadStartRVObject X kX lX hTX).domain
  let domY := (preparedHeadStartRVObject Y kY lY hTY).domain
  have memU : ∀ u : domX, (toMixed0 domX u).val ∈ U.carrier := fun u =>
    (mem_domain_labels hX lX hTX u.val).mp u.property
  let into : Map domX U := (toMixed0 domX).corestrict memU
  have memY : ∀ z : U', (fromMixed0 U' z).val ∈ domY.carrier := fun z =>
    (mem_domain_labels hY lY hTY _).mpr (mem_of_val z)
  let out : Map U' domY := (fromMixed0 U').corestrict memY
  let F : Map domX domY := out.comp (Φ.comp into)
  have hF_val (u : domX) : (F u).val = (Φ (into u)).val.2 := rfl
  have hinto : Function.Bijective into := by
    refine ⟨fun x y he => ?_, fun z => ?_⟩
    · have := congrArg (fun w : U => w.val.2) he
      exact Subtype.ext this
    · have hz : z.val.2 ∈ domX.carrier := (mem_domain_labels hX lX hTX _).mpr (mem_of_val z)
      refine ⟨⟨_, hz⟩, Subtype.ext (Prod.ext (Subsingleton.elim (α := Fin 0 → VF M) _ _) rfl)⟩
  have hout : Function.Bijective out := by
    refine ⟨fun x y he => ?_, fun v => ?_⟩
    · have h2 : x.val.2 = y.val.2 := congrArg Subtype.val he
      exact Subtype.ext (Prod.ext (Subsingleton.elim (α := Fin 0 → VF M) _ _) h2)
    · have hv : ((Fin.elim0, v.val) : Mixed M 0 qY) ∈ U'.carrier := (mem_domain_labels hY lY hTY _).mp v.property
      exact ⟨⟨_, hv⟩, rfl⟩
  have hF : Function.Bijective F := hout.comp (hΦ.comp hinto)
  refine cls_eq_of_volume hc h hdX hdY F hF (fun u => ?_) (fun u => ?_)
  · rw [volumeGamma_eq, volumeGamma_eq]
    change ∏ i, gam ((preparedHeadStartRVObject X kX lX hTX).value u i) =
      ∏ i, gam ((preparedHeadStartRVObject Y kY lY hTY).value (F u) i)
    rw [value_labels hX lX hTX, value_labels hY lY hTY]
    simp only [hF_val]
    exact hprod (into u)
  · obtain ⟨p, rfl⟩ := pureRVTagQuotient_surjective _ u
    obtain ⟨p', hp'⟩ := pureRVTagQuotient_surjective _ (F (pureRVTagQuotient _ p))
    have hpp : p'.val.2 = (Φ (into (pureRVTagQuotient _ p))).val.2 := congrArg Subtype.val hp'
    have hUp : (Fin.elim0, p.val.2) ∈ U.carrier := ((mem_bundle_labels hX lX p.val).mp p.property).1
    let z : U := ⟨(Fin.elim0, p.val.2), hUp⟩
    have hz : into (pureRVTagQuotient _ p) = z := Subtype.ext rfl
    have hUp' : (Fin.elim0, p'.val.2) ∈ U'.carrier := ((mem_bundle_labels hY lY p'.val).mp p'.property).1
    let z' : U' := ⟨(Fin.elim0, p'.val.2), hUp'⟩
    have hzz : Φ z = z' := by
      apply Subtype.ext
      refine Prod.ext (Subsingleton.elim (α := Fin 0 → VF M) _ _) ?_
      change (Φ z).val.2 = p'.val.2
      rw [hpp, hz]
    change (headStartRVForm X kX lX ηX hηX (pureRVTagQuotient _ p)).val =
      (headStartRVForm Y kY lY ηY hηY (F (pureRVTagQuotient _ p))).val
    rw [← hp', headStartRVForm_at, headStartRVForm_at]
    refine (hρX _ z ?_).trans ((hρ z).trans ?_)
    · rw [headStartBaseProjection_value]
    · rw [hzz]
      refine (hρY _ z' ?_).symm
      rw [headStartBaseProjection_value]

end Classes

end DiamondIntegral.Section7.MapClasses
