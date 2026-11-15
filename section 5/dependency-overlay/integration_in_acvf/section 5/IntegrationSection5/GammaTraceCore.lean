import IntegrationSection5.UniformRelativeTrace
import Section5.GammaRestriction

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
open SpecialTransformations.Section3
variable {G : GammaParameters.Base (M := M)} {S : Set M} {n m l N : ℕ}

structure GammaFibreFocusDefinable (G : GammaParameters.Base (M := M))
    {A : DefSet (M := M) S n m} {i : Fin n} {k : Fin m} (D : FibreFocusData A i k) : Prop where
  locus : GammaSetDefinable G D.locus
  center : GammaScalarGraphDefinable G (fun p x => p ∈ carrier A ∩ D.locus ∧ x = D.center p)

theorem gamma_fibre_eta_graph {A : DefSet (M := M) S n m} {j : Fin n} {k : Fin m}
    (D : FibreFocusData A j k) (hA : GammaSetDefinable G (carrier A)) (hD : GammaFibreFocusDefinable G D) :
    GammaGraphDefinable G (pointMapGraph D.etaMap) := by
  let hΓ := gammaLogicInput G
  have hs : GammaScalarGraphDefinable G
      (fun p x => p ∈ carrier A ∩ D.locus ∧ x = D.center p) := hD.center
  have hactive := hΓ.scalar_image_graph hs (affineGraphMap j G.real)
  have hinactive := hΓ.restrict_graph (hΓ.sdiff hA hD.locus)
    (hΓ.real_map_graph (Map.id (PresentedSet.univ (pointSpace n m) G.real)))
  apply GammaGraphDefinable.congr (hΓ.union_graph hactive hinactive)
  intro p q
  constructor
  · rintro (⟨a, x, ⟨ha, hx⟩, he⟩ | ⟨hp, a, ha, he⟩)
    · have hh := (affineGraphMap_apply j G.real a x).symm.trans he
      have hp : a = p := congrArg Prod.fst hh
      subst p
      have hq := congrArg Prod.snd hh
      refine ⟨⟨a, ha.1⟩, rfl, ?_⟩
      change D.eta a = q
      rw [FibreFocusData.eta, if_pos ha.2]
      exact (congrArg (fun y : VF (M := M) => replace j a (vfAt a j - y)) hx).symm.trans hq
    · have heq : p = q := ha.symm.trans he
      refine ⟨⟨p, hp.1⟩, rfl, ?_⟩
      change D.eta p = q
      rw [FibreFocusData.eta, if_neg hp.2]
      exact heq
  · rintro ⟨a, rfl, he⟩
    change D.eta a.val = q at he
    by_cases hl : a.val ∈ D.locus
    · left
      refine ⟨a.val, D.center a.val, ⟨⟨a.property, hl⟩, rfl⟩, ?_⟩
      have heta : D.eta a.val =
          replace j a.val (vfAt a.val j - D.center a.val) := by
        rw [FibreFocusData.eta, if_pos hl]
      exact (affineGraphMap_apply j G.real a.val (D.center a.val)).trans
        (Prod.ext rfl (heta.symm.trans he))
    · right
      refine ⟨⟨a.property, hl⟩, ⟨a.val, Set.mem_univ _⟩, rfl, ?_⟩
      have heta : D.eta a.val = a.val := by rw [FibreFocusData.eta, if_neg hl]
      exact heta.symm.trans he

def GammaUniformTrace {a b : ℕ} {A : DefSet (M := M) S n a} {B : DefSet (M := M) S n b} :
    UniformRelativeTrace S n A B → Prop
  | .nil A => GammaSetDefinable G (carrier A)
  | .canonical i tail => GammaSetDefinable G (carrier A) ∧ GammaUniformTrace tail
  | .focus D tail => GammaSetDefinable G (carrier A) ∧ GammaFibreFocusDefinable G D ∧ GammaUniformTrace tail

theorem gamma_fibre_focus_of_real {A : DefSet (M := M) G.real n m} {i : Fin n} {k : Fin m}
    (D : FibreFocusData A i k) : GammaFibreFocusDefinable G D := by
  refine ⟨(gammaLogicInput G).real_set D.locus D.locus_definable,?_⟩
  apply GammaScalarGraphDefinable.congr ((gammaLogicInput G).real_scalar_graph D.centerMap)
  intro p x
  constructor
  · rintro ⟨a,rfl,he⟩
    exact ⟨a.property,he.symm⟩
  · rintro ⟨hp,he⟩
    exact ⟨⟨p,hp⟩,rfl,he.symm⟩

theorem gamma_uniform_trace_of_real {A : DefSet (M := M) G.real n m} {B : DefSet (M := M) G.real n l}
    (T : UniformRelativeTrace G.real n A B) : GammaUniformTrace (G := G) T := by
  induction T with
  | nil A => exact (gammaLogicInput G).real_set _ (setDefinable A)
  | canonical i tail ih => exact ⟨(gammaLogicInput G).real_set _ (setDefinable _),ih⟩
  | focus D tail ih => exact ⟨(gammaLogicInput G).real_set _ (setDefinable _),gamma_fibre_focus_of_real D,ih⟩

end IntegrationInACVF.Section5
