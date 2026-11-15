import IntegrationSection5.PositionCoordinateGraph
import Section5.GammaLift

/-! A positioning bijection induces an actual original-base bijection
between arbitrary unary presentations with bijective VF projections. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
open IntegrationInACVF.Section4 IntegrationInACVF.Section4.Cells
open IntegrationInACVF.Section3ACVF
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {m l : ℕ}

def unaryPresentationEquiv
    (A : Set (Point (M := M) 1 m)) (B : Set (Point (M := M) 1 l))
    (D E : Set (VF (M := M)))
    (hA : Set.BijOn (fun p => vfAt p 0) A D)
    (hB : Set.BijOn (fun p => vfAt p 0) B E)
    (f : VF (M := M) → VF (M := M)) (hf : Set.BijOn f D E) : A ≃ B :=
  ((hA.equiv _).trans (hf.equiv f)).trans (hB.equiv _).symm

theorem unaryPresentationEquiv_vf
    (A : Set (Point (M := M) 1 m)) (B : Set (Point (M := M) 1 l))
    (D E : Set (VF (M := M)))
    (hA : Set.BijOn (fun p => vfAt p 0) A D)
    (hB : Set.BijOn (fun p => vfAt p 0) B E)
    (f : VF (M := M) → VF (M := M)) (hf : Set.BijOn f D E) (a : A) :
    vfAt (unaryPresentationEquiv A B D E hA hB f hf a).val 0 = f (vfAt a.val 0) := by
  have h := (hB.equiv _).apply_symm_apply ((hf.equiv f) ((hA.equiv _) a))
  exact congrArg (fun z : E => z.val) h

def unaryPresentationGammaIso
    (A : Set (Point (M := M) 1 m)) (B : Set (Point (M := M) 1 l))
    (hA : GammaSetDefinable G A) (hB : GammaSetDefinable G B)
    (D E : Set (VF (M := M)))
    (hAD : Set.BijOn (fun p => vfAt p 0) A D)
    (hBE : Set.BijOn (fun p => vfAt p 0) B E)
    (f : VF (M := M) → VF (M := M)) (hf : Set.BijOn f D E)
    (hfG : GammaParameters.DefinableOverBase G (fun _ : Fin 2 => .vf) (positionCodes D f)) :
    GammaIso G A B where
  equiv := unaryPresentationEquiv A B D E hAD hBE f hf
  graph := by
    let σ : Fin 2 → Fin ((1+m)+(1+l)) :=
      ![Fin.castAdd (1+l) (0 : Fin (1+m)),Fin.natAdd (1+m) (0 : Fin (1+l))]
    let C := {z : Fin ((1+m)+(1+l)) → M | z ∘ σ ∈ positionCodes D f}
    have hC : FullBaseAtomicity.OverBase (GammaBaseBridge.fullBase G) C :=
      FullBaseAtomicity.OverBase.preimage_comp (GammaBaseBridge.of_gamma G hfG) σ
    have h := GammaTupleGraphs.relation_of_full G C hC
    let L := gammaLogicInput G
    apply GammaGraphDefinable.congr
      (L.swap_graph (L.restrict_graph hB (L.swap_graph (L.restrict_graph hA h))))
    intro p q
    have hCode : Fin.append (gammaPointCode p) (gammaPointCode q) ∘ σ =
        ![(vfAt p 0).val,(vfAt q 0).val] := by
      funext j
      fin_cases j <;> simp [σ,gammaPointCode,vfAt]
      · exact Fin.append_left _ _ (0 : Fin 1)
      · exact Fin.append_left _ _ (0 : Fin 1)
    constructor
    · rintro ⟨hq,hp,hc⟩
      change Fin.append (gammaPointCode p) (gammaPointCode q) ∘ σ ∈ positionCodes D f at hc
      rw [hCode] at hc
      obtain ⟨x,hx,he⟩ := hc
      have hxp : x = vfAt p 0 := Subtype.ext (congrFun he 0).symm
      have hqf : vfAt q 0 = f (vfAt p 0) :=
        (Subtype.ext (congrFun he 1)).trans (congrArg f hxp)
      refine ⟨⟨p,hp⟩,rfl,?_⟩
      apply hBE.injOn (unaryPresentationEquiv A B D E hAD hBE f hf ⟨p,hp⟩).property hq
      exact (unaryPresentationEquiv_vf A B D E hAD hBE f hf ⟨p,hp⟩).trans hqf.symm
    · rintro ⟨a,rfl,rfl⟩
      refine ⟨(unaryPresentationEquiv A B D E hAD hBE f hf a).property,a.property,?_⟩
      change Fin.append (gammaPointCode a.val)
        (gammaPointCode (unaryPresentationEquiv A B D E hAD hBE f hf a).val) ∘ σ ∈ positionCodes D f
      rw [hCode]
      refine ⟨vfAt a.val 0,hAD.mapsTo a.property,?_⟩
      funext j
      fin_cases j
      · rfl
      · exact congrArg Subtype.val (unaryPresentationEquiv_vf A B D E hAD hBE f hf a)

end IntegrationInACVF.Section5
