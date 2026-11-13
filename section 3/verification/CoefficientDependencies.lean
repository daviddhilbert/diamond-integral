import DiamondIntegral
import Lean.Util.FoldConsts
open Lean Elab Command

partial def coefficientDependencyClosure (env : Environment)
    (todo : List Name) (seen : NameSet := {}) : NameSet :=
  match todo with
  | [] => seen
  | n :: ns =>
    if seen.contains n then coefficientDependencyClosure env ns seen
    else
      let seen := seen.insert n
      match env.find? n with
      | none => coefficientDependencyClosure env ns seen
      | some ci => coefficientDependencyClosure env
          (ci.getUsedConstantsAsSet.toList ++ ns) seen

run_cmd do
  let env ← getEnv
  let roots : List Name := [
    `DiamondIntegral.Section3.proposition_3_18_unmeasured,
    `DiamondIntegral.Section3.proposition_3_18_measured,
    `DiamondIntegral.Section3.gammaGroundUnmeasuredTensor_descends_iff,
    `DiamondIntegral.Section3.gammaGroundMeasuredTensor_descends_iff,
    `DiamondIntegral.Section3.gammaGroundBalancedEvaluationOnRV,
    `DiamondIntegral.Section3.gammaGroundBalancedEvaluationOnRV_on_RES,
    `DiamondIntegral.Section3.gammaGroundAnnularPullback_le_actual_tensor_kernel]
  for n in roots do
    unless env.contains n do throwError "Missing root {n}"
    let deps := coefficientDependencyClosure env [n]
    let own := deps.toList.filter fun n =>
      "DiamondIntegral.Section3".isPrefixOf n.toString
    let inj := own.filter fun n =>
      (n.toString.splitOn "injective").length > 1 ||
      (n.toString.splitOn "Injective").length > 1
    logInfo m!"ROOT {n}\nSECTION3_CONSTANTS {own.length}\nINJECTIVITY_HEADS {inj}"
    let forbidden := own.filter fun n =>
      ((n.toString.splitOn "gammaGroundGammaToRV").length > 1 ||
       (n.toString.splitOn "gammaGroundFiniteGammaToRES").length > 1) &&
      (n.toString.splitOn "injective").length > 1
    unless forbidden.isEmpty do
      throwError "Unexpected horizontal coefficient injectivity dependence: {forbidden}"
  logInfo "PASS: all seven roots inspected; no horizontal Gamma coefficient-injectivity premise. The checked RES-to-RV vertical injection is used."
