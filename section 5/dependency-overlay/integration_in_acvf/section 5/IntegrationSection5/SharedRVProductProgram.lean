import IntegrationSection5.SharedRVProductSource
import IntegrationSection5.ProductProgramVolume

/-! Actual two-stage shared-parameter product programs, their full Gamma certificates, exact joint kernels and volume formulas. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {S : Set M} {m b c : ℕ}
structure SharedRVProductProgram
    (H : DefSet (M := M) S 2 m)
    (AD AE : DefSet (M := M) S 1 m)
    (BD : DefSet (M := M) S 1 b) (BE : DefSet (M := M) S 1 c)
    (d : Map AD BD) (e : Map AE BE) where
  dSource : Map H AD
  eSource : Map H AE
  d_spec : ∀ a : H, (dSource a).val = activeUnaryProjection 0 id a.val
  e_spec : ∀ a : H, (eSource a).val = activeUnaryProjection 1 id a.val
  first : HeadPreparation H
  firstProjection : Fin b → Fin first.arity
  firstProjection_bijective : Function.Bijective firstProjection
  first_square : ∀ a : H, activeUnaryProjection 0 firstProjection (first.map a).val = (d (dSource a)).val
  first_graph : GammaGraphDefinable G (pointMapGraph first.map)
  first_target_gamma : GammaSetDefinable G (carrier first.target)
  tail : HeadPreparation first.contractedSet
  tailProjection : Fin c → Fin tail.arity
  retained_le : (1+first.arity) ≤ tail.arity
  tail_cover : ∀ j : Fin tail.arity, (∃ k, tailProjection k = j) ∨ ∃ k, suffixIndex retained_le k = j
  tail_square : ∀ a : H,
    activeUnaryProjection 0 tailProjection (tail.map (first.contractionMap a)).val = (e (eSource a)).val
  tail_graph : GammaGraphDefinable G (pointMapGraph tail.map)
  tail_target_gamma : GammaSetDefinable G (carrier tail.target)


end IntegrationInACVF.Section5

namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {S : Set M} {m b c : ℕ}

theorem sharedRV_product_contraction_program
    {AD AE : DefSet (M := M) S 1 m}
    {BD : DefSet (M := M) S 1 b} {BE : DefSet (M := M) S 1 c}
    (d : SpecialBijection AD BD) (e : SpecialBijection AE BE)
    (hd : GammaChainDefinable G d.chain) (he : GammaChainDefinable G e.chain)
    (hBD : IsRVPullback (carrier BD)) (hBE : IsRVPullback (carrier BE))
    (H : DefSet (M := M) S 2 m)
    (hH : carrier H = {p | activeUnaryProjection 0 id p ∈ carrier AD ∧
      activeUnaryProjection 1 id p ∈ carrier AE})
    (hHG : GammaSetDefinable G (carrier H)) :
    Nonempty (SharedRVProductProgram (G := G) H AD AE BD BE d.toMap e.toMap) := by
  have hHD (p : H) : activeUnaryProjection 0 id p.val ∈ carrier AD :=
    ((Set.ext_iff.mp hH p.val).mp p.property).1
  have hHE (p : H) : activeUnaryProjection 1 id p.val ∈ carrier AE :=
    ((Set.ext_iff.mp hH p.val).mp p.property).2
  let dSource : Map H AD := Map.corestrict (activeUnaryProjectionMap 0 id H) hHD
  let eSource : Map H AE := Map.corestrict (activeUnaryProjectionMap 1 id H) hHE
  let Q : Point (M := M) 2 m → Prop := fun p => activeUnaryProjection 1 id p ∈ carrier AE
  have hQ : ∀ p x, Q (replace 0 p x) ↔ Q p := by
    intro p x
    simp only [Q,activeUnaryProjection,replace,vfAt,Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)]
  obtain ⟨T,σD,hleD,hTG,hTmap,hσD,hCompat,hCover,hTshape,hTcomm⟩ :=
    sharedRV_unary_product_head_preparation d hd hBD H hHG id Q hQ hH
  have hFirst : ∀ a : H, activeUnaryProjection 0 σD (T.map a).val = (d.toMap (dSource a)).val :=
    hTcomm
  let ρE : Fin m → Fin (1+T.arity) := Fin.natAdd 1 ∘ suffixIndex hleD
  let Q' : Point (M := M) 1 (1+T.arity) → Prop := fun p => productHeadRVCondition BD σD p.2
  have hQ' : ∀ p x, Q' (replace 0 p x) ↔ Q' p := fun _ _ => Iff.rfl
  have hSource : carrier T.contractedSet =
      {p | activeUnaryProjection 0 ρE p ∈ carrier AE ∧ Q' p} :=
    sharedRV_product_head_contracted_shape AE BD T.target σD (suffixIndex hleD) hTshape
  obtain ⟨U,σE,hleE,hUG,hUmap,hσE,hCompatE,hCoverE,hUshape,hUcomm⟩ :=
    sharedRV_unary_product_head_preparation e he hBE T.contractedSet
      (gamma_headImage T.target hTG) ρE Q' hQ' hSource
  have hInput (a : H) : activeUnaryProjection 0 ρE (T.contractionMap a).val =
      activeUnaryProjection 1 id a.val := by
    apply Prod.ext
    · funext j
      fin_cases j
      change vfAt (headKeyMap T.target (T.map a)).val 0 = vfAt a.val 1
      rw [headKeyMap_apply]
      exact specialRelative_unaryRelative T.special a 1 (by decide)
    · funext j
      change (headKeyMap T.target (T.map a)).val.2 (Fin.natAdd 1 (suffixIndex hleD j)) = a.val.2 j
      rw [headKeyMap_apply]
      change Fin.append (fun _ : Fin 1 => rv (vfAt (T.map a).val 0))
        (T.map a).val.2 (Fin.natAdd 1 (suffixIndex hleD j)) = a.val.2 j
      rw [Fin.append_right]
      exact specialRelative_oldLabels T.special a j
  have hSecond : ∀ a : H,
      activeUnaryProjection 0 σE (U.map (T.contractionMap a)).val = (e.toMap (eSource a)).val := by
    intro a
    rw [hUcomm]
    apply congrArg (fun x : AE => (e.toMap x).val)
    exact Subtype.ext (hInput a)
  exact ⟨{
    dSource := dSource
    eSource := eSource
    d_spec := fun _ => rfl
    e_spec := fun _ => rfl
    first := T
    firstProjection := σD
    firstProjection_bijective := hσD Function.bijective_id
    first_square := hFirst
    first_graph := hTmap
    first_target_gamma := hTG
    tail := U
    tailProjection := σE
    retained_le := hleE
    tail_cover := hCoverE
    tail_square := hSecond
    tail_graph := hUmap
    tail_target_gamma := hUG }⟩

end IntegrationInACVF.Section5

namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {S : Set M} {m b c : ℕ}
namespace SharedRVProductProgram
variable {H : DefSet (M := M) S 2 m} {AD AE : DefSet (M := M) S 1 m}
variable {BD : DefSet (M := M) S 1 b} {BE : DefSet (M := M) S 1 c}
variable {d : Map AD BD} {e : Map AE BE}

def program (P : SharedRVProductProgram (G := G) H AD AE BD BE d e) :
    OrderedContractionProgram S H (headImage P.tail.target) :=
  .step P.first (.step P.tail (.zero (headImage P.tail.target)))

theorem gamma_program (P : SharedRVProductProgram (G := G) H AD AE BD BE d e) :
    GammaProgramDefinable G P.program :=
  ⟨P.first_graph,P.first_target_gamma,P.tail_graph,P.tail_target_gamma,
    gamma_headImage P.tail.target P.tail_target_gamma⟩

end SharedRVProductProgram
namespace SharedRVProductProgram
variable {H : DefSet (M := M) S 2 m} {AD AE : DefSet (M := M) S 1 m}
variable {BD : DefSet (M := M) S 1 b} {BE : DefSet (M := M) S 1 c}
variable {d : Map AD BD} {e : Map AE BE}

theorem kernel_formula (P : SharedRVProductProgram (G := G) H AD AE BD BE d e) (a b : H) :
    P.program.toMap a = P.program.toMap b ↔
      SameRV (d (P.dSource a)).val (d (P.dSource b)).val ∧
        SameRV (e (P.eSource a)).val (e (P.eSource b)).val := by
  change P.tail.contractionMap (P.first.contractionMap a) =
    P.tail.contractionMap (P.first.contractionMap b) ↔ _
  rw [unary_contractionMap_eq_iff,
    lifted_unary_sameRV_iff P.tail.map P.tail.special P.retained_le P.tailProjection P.tail_cover,
    P.tail_square a,P.tail_square b]
  have hlabels (a : H) : (P.first.contractionMap a).val.2 = (headKey (P.first.map a).val).2 :=
    congrArg Prod.snd (headKeyMap_apply P.first.target (P.first.map a))
  rw [hlabels a,hlabels b,headKey_labels_projection_iff P.firstProjection P.firstProjection_bijective.2,
    P.first_square a,P.first_square b]
  exact and_comm

end SharedRVProductProgram
namespace SharedRVProductProgram
variable {H : DefSet (M := M) S 2 m} {AD AE : DefSet (M := M) S 1 m}
variable {BD : DefSet (M := M) S 1 b} {BE : DefSet (M := M) S 1 c}
variable {d : Map AD BD} {e : Map AE BE}

theorem volumeIndex_zero (P : SharedRVProductProgram (G := G) H AD AE BD BE d e) :
    P.program.volumeIndex 0 = Fin.natAdd 1 (suffixIndex P.retained_le 0) := by
  apply Fin.ext
  change (1+P.tail.arity)-(1+P.first.arity)+0 = 1+(P.tail.arity-(1+P.first.arity)+0)
  have h := P.retained_le
  omega

theorem volumeIndex_one (P : SharedRVProductProgram (G := G) H AD AE BD BE d e) :
    P.program.volumeIndex 1 = 0 := by
  apply Fin.ext
  change (1+P.tail.arity)-(1+P.tail.arity)+0 = 0
  omega

theorem volume_formula (P : SharedRVProductProgram (G := G) H AD AE BD BE d e) (a : H) :
    (rvObjectVolume P.program.contractionObject (P.program.rawContractionMap a)).val =
      ![rv (vfAt (d (P.dSource a)).val 0),rv (vfAt (e (P.eSource a)).val 0)] := by
  funext j
  fin_cases j
  · change (P.program.toMap a).val.2 (P.program.volumeIndex 0) = _
    rw [P.volumeIndex_zero]
    change (headKeyMap P.tail.target (P.tail.map (P.first.contractionMap a))).val.2
      (Fin.natAdd 1 (suffixIndex P.retained_le 0)) = _
    rw [headKeyMap_apply]
    change Fin.append (fun _ : Fin 1 => rv (vfAt (P.tail.map (P.first.contractionMap a)).val 0))
      (P.tail.map (P.first.contractionMap a)).val.2 (Fin.natAdd 1 (suffixIndex P.retained_le 0)) = _
    rw [Fin.append_right,specialRelative_oldLabels P.tail.special]
    change (headKeyMap P.first.target (P.first.map a)).val.2 0 = _
    rw [headKeyMap_apply]
    change rv (vfAt (P.first.map a).val 0) = rv (vfAt (d (P.dSource a)).val 0)
    exact congrArg (fun p : Point (M := M) 1 b => rv (vfAt p 0)) (P.first_square a)
  · change (P.program.toMap a).val.2 (P.program.volumeIndex 1) = _
    rw [P.volumeIndex_one]
    change (headKeyMap P.tail.target (P.tail.map (P.first.contractionMap a))).val.2 0 = _
    rw [headKeyMap_apply]
    change rv (vfAt (P.tail.map (P.first.contractionMap a)).val 0) = rv (vfAt (e (P.eSource a)).val 0)
    exact congrArg (fun p : Point (M := M) 1 c => rv (vfAt p 0)) (P.tail_square a)

end SharedRVProductProgram

end IntegrationInACVF.Section5
