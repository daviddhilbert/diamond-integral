import «section 6».FocusCutoffValueMaps

/-! Complete scalar product and Gamma cutoff maps for two varying VF
maps. Equal coefficient and focus leading terms give the same actual
radius without replacing a varying coefficient by a named constant. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

def scalarExtensionVFValue (f : Map A (DefSet.univ (rawVFSpace (M := M) 1) S))
    (p : Mixed M n r) : VF M :=
  ⟨scalarCodeExtension f (mixedValues p),scalarCodeExtension_isVF f _⟩

theorem scalarExtensionVFValue_at (f : Map A (DefSet.univ (rawVFSpace (M := M) 1) S)) (p : A) :
    scalarExtensionVFValue f p.val=(f p).val 0 := Subtype.ext (scalarCodeExtension_at f p)

def scalarPointwiseProductMap
    (f g : Map A (DefSet.univ (rawVFSpace (M := M) 1) S)) :
    Map A (DefSet.univ (rawVFSpace (M := M) 1) S) := by
  let P := rawMixedSpace (M := M) n r
  let Q := rawVFSpace (M := M) 1
  let F (z : Fin n ⊕ Fin r → M) : Fin 1 → M := fun _ =>
    iVFMul (scalarCodeExtension f z) (scalarCodeExtension g z)
  let value (p : Mixed M n r) : Fin 1 → VF M := fun _ =>
    scalarExtensionVFValue f p*scalarExtensionVFValue g p
  have hF : S.DefinableMap LRV F := fun _ =>
    scalarMulCode_definable (scalarCodeExtension_definable f) (scalarCodeExtension_definable g)
  have hCode (z : P.domain) : vfValues (value (P.decode z))=F z.val := by
    change (fun _ => iVFMul (scalarCodeExtension f (mixedValues (P.decode z)))
      (scalarCodeExtension g (mixedValues (P.decode z))))=F z.val
    rw [mixedValues_decode]
  have hDom (z : P.domain) : F z.val ∈ Q.domain := ⟨value (P.decode z),hCode z⟩
  exact Map.ofCodes A value F hF hDom
    (fun z => vfValues_injective ((vfValues_decode _).trans (hCode z).symm))

theorem scalarPointwiseProductMap_value
    (f g : Map A (DefSet.univ (rawVFSpace (M := M) 1) S)) (p : A) :
    (scalarPointwiseProductMap f g p).val 0=(f p).val 0*(g p).val 0 := by
  change scalarExtensionVFValue f p.val*scalarExtensionVFValue g p.val=_
  rw [scalarExtensionVFValue_at,scalarExtensionVFValue_at]

def scalarPointwiseGammaProductMap
    (f g : Map A (DefSet.univ (rawVFSpace (M := M) 1) S)) :
    Map A (DefSet.univ (rawGammaPresentation (M := M)) S) :=
  (scalarGammaValueMap S).comp (scalarPointwiseProductMap f g)

theorem scalarPointwiseGammaProductMap_value
    (f g : Map A (DefSet.univ (rawVFSpace (M := M) 1) S)) (p : A)
    (hf : (f p).val 0 ≠ 0) (hg : (g p).val 0 ≠ 0) :
    (scalarPointwiseGammaProductMap f g p).val.val=vfValue ((f p).val 0*(g p).val 0) := by
  have hn : (scalarPointwiseProductMap f g p).val 0 ≠ 0 := by
    rw [scalarPointwiseProductMap_value]
    exact mul_ne_zero hf hg
  exact (scalarGammaValueMap_nonzero S _ hn).trans
    (congrArg vfValue (scalarPointwiseProductMap_value f g p))

theorem scalarPointwiseGammaProductMap_rv_congr
    (f g : Map A (DefSet.univ (rawVFSpace (M := M) 1) S))
    (hf : ∀ p : A,(f p).val 0 ≠ 0) (hg : ∀ p : A,(g p).val 0 ≠ 0)
    (p q : A) (hF : rv M ((f p).val 0)=rv M ((f q).val 0))
    (hG : rv M ((g p).val 0)=rv M ((g q).val 0)) :
    (scalarPointwiseGammaProductMap f g p).val=(scalarPointwiseGammaProductMap f g q).val := by
  apply Subtype.ext
  rw [scalarPointwiseGammaProductMap_value f g p (hf p) (hg p),
    scalarPointwiseGammaProductMap_value f g q (hf q) (hg q)]
  have hFV : vfValue ((f p).val 0)=vfValue ((f q).val 0) := congrArg Values.vrv hF
  have hGV : vfValue ((g p).val 0)=vfValue ((g q).val 0) := congrArg Values.vrv hG
  change Values.vfValueHom _=Values.vfValueHom _
  rw [map_mul,map_mul]
  exact congrArg₂ (fun x y : GammaInfinity M => x*y) hFV hGV

end DiamondIntegral.Section6
