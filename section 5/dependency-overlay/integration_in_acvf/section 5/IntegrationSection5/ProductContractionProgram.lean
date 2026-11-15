import IntegrationSection5.ProductContractionSource
import IntegrationSection5.ProductContractionKernels
import IntegrationSection5.UnaryCoordinateSourceMap
import IntegrationSection5.GammaOrderedContraction

/-! An actual two-stage contraction of a product, constructed from actual
unary special preparations of its two factors. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {S : Set M} {b c : ℕ}

structure ProductContractionProgram
    (H : DefSet (M := M) S 2 0)
    (AD AE : DefSet (M := M) S 1 0)
    (BD : DefSet (M := M) S 1 b) (BE : DefSet (M := M) S 1 c)
    (d : Map AD BD) (e : Map AE BE) where
  dSource : Map H AD
  eSource : Map H AE
  d_spec : ∀ a : H, vfAt (dSource a).val 0 = vfAt a.val 0
  e_spec : ∀ a : H, vfAt (eSource a).val 0 = vfAt a.val 1
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

theorem product_contraction_program (D E : Set (VF (M := M)))
    {AD AE : DefSet (M := M) S 1 0}
    {BD : DefSet (M := M) S 1 b} {BE : DefSet (M := M) S 1 c}
    (hAD : carrier AD = vfUnarySet D) (hAE : carrier AE = vfUnarySet E)
    (d : SpecialBijection AD BD) (e : SpecialBijection AE BE)
    (hd : GammaChainDefinable G d.chain) (he : GammaChainDefinable G e.chain)
    (hBD : IsRVPullback (carrier BD)) (hBE : IsRVPullback (carrier BE))
    (H : DefSet (M := M) S 2 0) (hH : carrier H = cellPointSet (D ×ˢ E))
    (hHG : GammaSetDefinable G (carrier H)) :
    Nonempty (ProductContractionProgram (G := G) H AD AE BD BE d.toMap e.toMap) := by
  have hHD : ∀ p ∈ carrier H, activeUnaryProjection 0 Fin.elim0 p ∈ carrier AD := by
    intro p hp
    rw [hAD]
    exact ((Set.ext_iff.mp hH p).mp hp).1
  have hHE : ∀ p ∈ carrier H, activeUnaryProjection 1 Fin.elim0 p ∈ carrier AE := by
    intro p hp
    rw [hAE]
    exact ((Set.ext_iff.mp hH p).mp hp).2
  let dSource := unaryCoordinateSourceMap AD H 0 hHD
  let eSource := unaryCoordinateSourceMap AE H 1 hHE
  obtain ⟨T,σD,hσD,hTG,hTmap,hTshape,hTcomm⟩ := product_head_stage D E hAD d hd hBD H hH hHG
  have hFirst : ∀ a : H, activeUnaryProjection 0 σD (T.map a).val = (d.toMap (dSource a)).val := by
    intro a
    obtain ⟨x,hx,hcomm⟩ := hTcomm a
    have heq : x = dSource a := unary_zeroRV_ext hx
    exact heq ▸ hcomm
  let Q : Point (M := M) 1 (1+T.arity) → Prop := fun p => productHeadRVCondition BD σD p.2
  have hQ : ∀ p x, Q (replace 0 p x) ↔ Q p := fun _ _ => Iff.rfl
  have hShape := product_head_contracted_shape E BD T.target σD hTshape
  have hSource : carrier T.contractedSet =
      {p | activeUnaryProjection 0 Fin.elim0 p ∈ carrier AE ∧ Q p} := by
    change carrier (headImage T.target) = _
    rw [hShape,hAE]
    rfl
  obtain ⟨U,σE,hle,hUG,hUmap,_,hCover,hUshape,hUcomm⟩ :=
    unary_product_head_preparation e he hBE T.contractedSet (gamma_headImage T.target hTG) Q hQ hSource
  have hSecond : ∀ a : H,
      activeUnaryProjection 0 σE (U.map (T.contractionMap a)).val = (e.toMap (eSource a)).val := by
    intro a
    rw [hUcomm]
    apply congrArg (fun x : AE => (e.toMap x).val)
    apply unary_zeroRV_ext
    change vfAt (T.contractionMap a).val 0 = vfAt a.val 1
    change vfAt (headKeyMap T.target (T.map a)).val 0 = vfAt a.val 1
    rw [headKeyMap_apply]
    exact specialRelative_unaryRelative T.special a 1 (by decide)
  exact ⟨{
    dSource := dSource
    eSource := eSource
    d_spec := fun _ => rfl
    e_spec := fun _ => rfl
    first := T
    firstProjection := σD
    firstProjection_bijective := hσD
    first_square := hFirst
    first_graph := hTmap
    first_target_gamma := hTG
    tail := U
    tailProjection := σE
    retained_le := hle
    tail_cover := hCover
    tail_square := hSecond
    tail_graph := hUmap
    tail_target_gamma := hUG }⟩

namespace ProductContractionProgram
variable {H : DefSet (M := M) S 2 0} {AD AE : DefSet (M := M) S 1 0}
variable {BD : DefSet (M := M) S 1 b} {BE : DefSet (M := M) S 1 c}
variable {d : Map AD BD} {e : Map AE BE}

def program (P : ProductContractionProgram (G := G) H AD AE BD BE d e) :
    OrderedContractionProgram S H (headImage P.tail.target) :=
  .step P.first (.step P.tail (.zero (headImage P.tail.target)))

theorem gamma_program (P : ProductContractionProgram (G := G) H AD AE BD BE d e) :
    GammaProgramDefinable G P.program :=
  ⟨P.first_graph,P.first_target_gamma,P.tail_graph,P.tail_target_gamma,
    gamma_headImage P.tail.target P.tail_target_gamma⟩

end ProductContractionProgram
end IntegrationInACVF.Section5
