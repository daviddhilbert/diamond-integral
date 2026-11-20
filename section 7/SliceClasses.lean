import «section 7».FibreComparison
import «section 7».HeadStartK

/-! Head-start objects over a fibre (for Lemma 7.23 with `n > 2`).

The two stages of a standard contraction, restricted to the slice over a good
point `b`, end on the RV fibre of the second-stage set `B` over `b`. A
head-start object whose RV target is that fibre, with the two leading labels as
volume labels and the form of `B`, has the class of the fibre object of `B` at
`b` (`cls_labelObject_fibre`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.SliceClasses
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.ChartOfMeasured
open DiamondIntegral.Section7.FiberwiseInput DiamondIntegral.Section7.FirstStage
open DiamondIntegral.Section7.FibreObjects DiamondIntegral.Section7.KernelBaseChange

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) {T : LRV.Substructure M}
variable {m q k a kX : ℕ} (b : Fin m → VF M)
variable {B : DefSet (rawMixedSpace (M := M) m q) (T : Set M)}
variable {ωB : Map B (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M))}
variable {X : DefSet (rawMixedSpace (M := M) a q) (adjoin T b : Set M)}
variable {U : DefSet (rawMixedSpace (M := M) 0 q) (adjoin T b : Set M)} {ν : Fin a → Fin q}

/-- **A head-start object over a fibre has the class of the fibre object.** -/
theorem cls_labelObject_fibre (h : a + kX = k)
    (hX : ∀ p : Mixed M a q, p ∈ X.carrier ↔ (Fin.elim0, p.2) ∈ U.carrier ∧ ∀ i, rv M (p.1 i) = p.2 (ν i))
    (lX : Fin kX → Fin q) (ρ : Fin k → Fin q)
    (hU : ∀ w : Fin q → RVInfinity M, (Fin.elim0, w) ∈ U.carrier ↔ (b, w) ∈ B.carrier)
    (hprod : ∀ f : Fin q → Gamma M, ∏ i, f (Fin.append ν lX i) = ∏ i, f (ρ i))
    (hFin : ∀ t : Fin k → RVInfinity M, {u : Fin q → RVInfinity M | (b, u) ∈ B.carrier ∧ u ∘ ρ = t}.Finite)
    (hNZ : ∀ p ∈ B.carrier, ∀ i, (p.2 (ρ i)).val ≠ iRVZero)
    (ρU : Map U (DefSet.univ (rawGammaPresentation (M := M)) (adjoin T b : Set M)))
    (hρU : ∀ (z : U) (hz : (b, z.val.2) ∈ B.carrier), (ρU z).val = (ωB ⟨(b, z.val.2), hz⟩).val)
    (hTX : ∀ p ∈ X.carrier, ∀ z ∈ X.carrier, p.2 = z.2 → tupleRV M p.1 = tupleRV M z.1)
    (hfinX hnzX)
    (ηX : Map X (DefSet.univ (rawGammaPresentation (M := M)) (adjoin T b : Set M))) (hηX)
    (hρX : ∀ (p : X) (z : U), z.val.2 = p.val.2 → (ηX p).val = (ρU z).val)
    (hdX : (labelObject X kX lX hTX hfinX hnzX ηX hηX).doublyBounded)
    (hdF : (fibreObject T B ωB b ρ hFin hNZ).doublyBounded) :
    cls (objOf hc (adjoin T b) (labelObject X kX lX hTX hfinX hnzX ηX hηX) hdX) =
      castCls h.symm (cls (objOf hc (adjoin T b) (fibreObject T B ωB b ρ hFin hNZ) hdF)) := by
  subst h
  let domX := (preparedHeadStartRVObject X kX lX hTX).domain
  have hsub : domX.carrier ⊆ (fibreObject T B ωB b ρ hFin hNZ).object.domain.carrier := fun u hu =>
    (mem_fibreDomain B b u).mpr ((hU u).mp ((mem_domain_labels hX lX hTX u).mp hu))
  let F := Map.inclusion hsub
  have hF : Function.Bijective F := by
    refine ⟨fun x y he => ?_, fun v => ?_⟩
    · apply Subtype.ext
      have := congrArg Subtype.val he
      exact this
    have hv : v.val ∈ domX.carrier :=
      (mem_domain_labels hX lX hTX v.val).mpr ((hU v.val).mpr ((mem_fibreDomain B b v.val).mp v.property))
    exact ⟨⟨v.val, hv⟩, rfl⟩
  refine cls_eq_of_volume hc rfl hdX hdF F hF (fun u => ?_) (fun u => ?_)
  · rw [volumeGamma_eq, volumeGamma_eq]
    change ∏ i, gam ((preparedHeadStartRVObject X kX lX hTX).value u i) =
      ∏ i, gam ((fibreRVObject B b ρ).value ⟨u.val, _⟩ i)
    rw [value_labels hX lX hTX, fibreRVObject_value]
    exact hprod (fun l => gam (u.val l))
  · obtain ⟨p, rfl⟩ := pureRVTagQuotient_surjective _ u
    have hUp : (Fin.elim0, p.val.2) ∈ U.carrier := ((mem_bundle_labels hX lX p.val).mp p.property).1
    let z : U := ⟨(Fin.elim0, p.val.2), hUp⟩
    have hzB : (b, p.val.2) ∈ B.carrier := (hU _).mp hUp
    change (headStartRVForm X kX lX ηX hηX (pureRVTagQuotient _ p)).val =
      (fibreForm B ωB b ⟨p.val.2, (mem_fibreDomain B b _).mpr hzB⟩).val
    rw [headStartRVForm_at, fibreForm_apply B ωB b p.val.2 hzB]
    refine (hρX _ z ?_).trans (hρU z hzB)
    rw [headStartBaseProjection_value]

end DiamondIntegral.Section7.SliceClasses
