#!/usr/bin/env python3
"""Build the entry point and audit complete §4 declaration types and axioms."""
from pathlib import Path
import hashlib
import json
import re
import subprocess

SECTION = Path(__file__).resolve().parent
ROOT = SECTION.parent
RECORD = SECTION / 'verification'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
INPUT_DEFINITIONS = {
    'DiamondIntegral.Section4.Section3GammaAffineInput.Input': 'section 4/Section3GammaAffineInput.lean',
    'DiamondIntegral.Section2.GammaPiecewiseRationalAffineInput': 'section 2/CitedGammaLinearity.lean',
    'DiamondIntegral.Section2.NontrivialDefinableGamma': 'section 2/AtomicBaseChange.lean',
}
MODULES = ['ReviewCalculations', 'StepFunctions', 'EulerGenerators', 'EulerFunctions',
           'EulerDecomposition', 'EulerBreakpoints', 'EulerConstantRegions', 'EulerGerms', 'EulerEnumeratedExpansion', 'EulerControlledBreakpoints', 'FiniteOrderRanks', 'EulerPointwise', 'EulerIntervals', 'EulerReflection', 'EulerOrderTransport', 'EulerUnaryPushforward', 'EulerFibreIntegral', 'EulerUnaryProjection', 'EulerKernelFubini', 'EulerCylindricalStrips', 'EulerRationalBranches', 'EulerRationalProjection', 'EulerPowerLawFibres', 'EulerConvolution', 'EulerIntervalProducts',
           'EulerBoundedSupport', 'EulerBoundedComparison', 'EulerTruncation', 'EulerBoundedGenerators', 'EulerBoundedQuotient', 'EulerFiniteCuts', 'EulerCutCellValues', 'EulerFiniteSets', 'GammaDefinableEuler', 'GammaOrderLogic', 'GammaRelationLogic', 'GammaQuantifierLogic', 'GammaFormulaLogic', 'GammaGermLogic', 'GammaGermFamilies', 'GammaFibreCounting', 'GammaTupleCounting', 'GammaUniformFiniteFibres', 'GammaWeightedBoundary', 'GammaCanonicalExpansion', 'GammaUnaryProjection', 'GammaKernelDecomposition', 'GammaFubiniTwo', 'GammaParametricFubini', 'GammaSortedFibres', 'GammaFiniteGraphPartition', 'GammaDefinableMaps', 'GammaBaseExtension', 'GammaParameterExtension', 'GammaFamilySlices', 'GammaFamilySlicesTwo', 'GammaUniformCuts', 'GammaFamilyBoundary', 'GammaFamilyEuler', 'GammaFamilyCutLogic', 'GammaFamilyIntegration', 'GammaIntegerFamilies', 'GammaIndicators', 'GammaIteratedIntegral', 'GammaPartialEvaluation', 'GammaPartialMaps', 'GammaWeightedFamilies', 'GammaFibreIntegralCongruence', 'GammaCoordinatePullback', 'FinitePermutationGeneration', 'FiniteTupleBlocks', 'FiniteTupleGraphProduct', 'RVRealProducts', 'RVCoordinateMaps', 'RVForgetScissors', 'RVUnderlyingIsomorphisms', 'RVUnderlyingProducts', 'RVMeasuredProduct', 'RVMeasuredProductProperties', 'RESChartRing', 'PolynomialDiagonal', 'PolynomialCoactionGrading', 'PointLocalizationNormalization', 'PointLocalizationEquivalence', 'RESPointLocalization', 'TensorPolynomialCoaction', 'TensorCoactionGrading', 'TensorZeroDegree', 'RVBalancedGradings', 'RVBalancedSpecialGradings', 'RVBalancedRadiusIdeal', 'RVBalancedRadiusQuotient', 'RVBalancedRadiusDegreeZero', 'RVBalancedZeroDegree', 'RVComparisonKernels', 'RVBalancedRadiusChoices', 'RVBalancedMapGradings', 'RVVolumeIsoEvaluation', 'RVTranslationEvaluation', 'RVTranslationIdeals', 'TensorGradedMaps', 'RestrictedPolynomialGrading', 'GammaPolynomialGradings', 'RESPsiGradings', 'RVChartRing', 'RVGrading', 'RVBoundedCharts', 'RVChartMaps', 'RVZeroDegreeRES', 'RVFiniteWeightedCounts', 'RVZeroWeightedCount', 'RESWeightEmbedding', 'RVZeroDegreeRetraction', 'RVZeroDegreeEquivalences', 'PositiveIdealDegreeZero', 'ReductionDegreeZero', 'RVBoundedRing', 'RVBoundedGrading', 'RVBoundedMaps', 'RVRadiusIdeal', 'RVRadiusQuotient', 'RESOrdinaryPoints', 'RESPointTuples', 'RESPointIdentification', 'RESHomogenization', 'RESDimensionFreeRing', 'RESDimensionFreeReduction', 'RESRingCoaction', 'RESGrading', 'RESOrdinaryUniversal', 'RESOrdinaryGrading', 'RESReductionGradings', 'PolynomialCoactionQuotient', 'CoactionGradedMaps', 'CoactionKernel', 'RESOrdinaryRing', 'RESBoundedPsi', 'RESBoundedFiniteBalancing', 'GammaBoundedSingletonProfiles', 'RESOrdinaryReduction', 'RESUnboundedPsi', 'RESFiniteBalancing', 'RESMeasuredReduction', 'RESFibreObjects', 'RVWeightScaling', 'RESWeightCharacter', 'RVVolumeMaps', 'FiniteTupleRotation', 'GammaBlockSlices', 'GammaPrefixIntegration', 'GammaGraphIntegration', 'GammaUnaryFamilyBridge', 'GammaHigherPushforward', 'GammaBoundedFamilies', 'FiniteTupleSwap', 'GammaBlockFubini', 'GammaIntegralCongruence', 'GammaMapOrder', 'GammaRadius', 'GammaRadiusProfiles', 'GammaHigherProjection', 'GammaSymmetricTruncation', 'GammaBoxStabilization', 'GammaProfileBijections', 'GammaConstantPushforward', 'GammaCounterweightedRay', 'GammaMeasuredProfileInvariance', 'GammaPushforwardSupport', 'GammaBoundedProfiles', 'GammaBoundedMapImage', 'GammaBoundedProfileRange', 'GammaProfileRestrictions', 'GammaZeroDegreeProfile', 'GammaObjectPolynomial', 'GammaSingletonProfiles', 'GammaSumMap', 'GammaSumFibres', 'GammaPushforwardConvolution', 'GammaProfileProducts', 'GammaObjectMultiplication', 'GammaObjectRelations', 'GammaCellSections', 'GammaCellUnboundedSections', 'GammaFinitePartitions', 'GammaCellFormula', 'GammaWeightedCharts', 'GammaChartOperations', 'GammaChartPresentation', 'GammaBoundedPolynomial', 'GammaBoundedProducts', 'GammaBoundedObjectPolynomial', 'GammaBoundedSpecialization', 'EulerEndpointProjection', 'GammaEndpointProjection', 'GammaUnboundedSpecialization', 'GammaUnboundedAssignments', 'GammaBoundedChartMap', 'GammaBoundedChartComparison', 'GammaChartSpecializations', 'GammaSpecializationComparison', 'GammaCylindricalCells', 'GammaReflectedFamilies', 'GammaProfileScissors', 'GammaPushforwardCongruence', 'GammaProductFamilies', 'GammaBijectiveRelations', 'GammaPointFamilies', 'GammaWeightProfiles', 'GammaFubiniPermutation', 'GammaPowerLawCells', 'GammaUnaryPowerPushforward', 'GammaPowerLawBijections', 'GammaUnaryBijections', 'GammaUnaryDescent', 'GammaWeightedPushforward', 'GammaUnaryPushforwardMap', 'GammaEulerSets', 'GammaFunctionProvenance', 'GammaDefinableFunctions', 'GammaGroupNames', 'GammaNamesSubgroup', 'GammaNamedRoots', 'GammaRVLifts', 'GammaRVChartPresentation', 'GammaTupleMaps', 'GammaTranslation', 'GammaTranslationCharts', 'GammaBoundedTranslationCharts', 'RVMeasuredCharts', 'RVMeasuredBounds', 'RVRadiusBounds', 'RVRadiusGenerators', 'RVMeasuredGroup', 'RVSharpCharts', 'RVSharpProducts', 'RVSharpScissors', 'GammaRVUniversal', 'GammaRVGrading', 'GammaRVMapGradings', 'GammaEulerEvaluation', 'GammaEulerBoundedComparison', 'GammaEulerPolynomialMaps', 'GammaOrdinaryEvaluation', 'GammaOrdinaryBoundedComparison', 'RVBoundedTensorComparison', 'RVBoundedOrdinaryEvaluation', 'RESAffineLocalization', 'RVBoundedOrdinaryRadius', 'GammaOrdinarySpecialClasses', 'RVOrdinaryTensorEvaluation', 'RVOrdinarySpecialValues', 'RVOrdinaryDimensionFreeEvaluation', 'GammaBoundedRVCharts', 'GammaBoundedRVPresentation', 'GammaBoundedRVEmpty', 'GammaBoundedRVMaps', 'GammaBoundedRVGrading', 'GammaBoundedRVProfiles', 'RVBoundedTensor', 'RVRadiusTensor', 'GammaUnaryIdentityProfile', 'GammaFiniteNames', 'GammaTupleSingletonProfiles', 'GammaFiniteBounds', 'GammaRVIdentityIso', 'GammaNameTuples', 'GammaFiniteRVCharts', 'GammaFiniteRVPresentation', 'GammaFiniteRVGrading', 'GammaFiniteRVMaps', 'GammaFiniteDecomposition', 'GammaFiniteGenerators', 'GammaFiniteRVMapGradings', 'GammaZeroDegreeFinite', 'RESFiniteUnitBalancing', 'RESAllFiniteBalancing', 'RESAllBoundedFiniteBalancing', 'FiniteGammaAlgebras', 'RVFiniteBalancedTensor', 'RVBoundedBalancedTensor', 'RVBalancedSpecialClasses', 'RVMeasuredTensor', 'RVMeasuredSpecialClasses', 'RVSharpRingMap', 'RVPointChoices', 'GammaRadiusAnnulus', 'GammaPointAlgebra', 'GammaFunctionPolynomial', 'GammaDefinableConvolution', 'GammaFunctionRing', 'GammaBoundedFunctions', 'GammaBoundedComparison', 'GammaBoundedQuotient', 'RVOrdinaryRing', 'RVOrdinaryGrading', 'RVOrdinaryMaps', 'RVNamedMultiplication', 'RVScaledRays', 'RVOrdinarySharpScissors', 'RVOrdinaryRadius', 'RVMeasuredScaling', 'RVOrdinaryMapGradings', 'RVMeasuredRadius', 'RVMeasuredPQuotient', 'RVOrdinaryPNormalization', 'RVMeasuredPDegreeZero', 'RVOrdinaryDegreeZero', 'RingHomGluing', 'RESAlternativeReduction', 'GammaAlternativeSpecialization', 'RESAlternativeForget', 'RESAlternativePsi', 'GammaAlternativeEvaluation', 'RVAlternativeTensorEvaluation', 'GammaAlternativeMaps', 'RESAlternativeCompatibility', 'RESAlternativeRawQuotient', 'RESAffineNormalization', 'RVAffineTensorEvaluation', 'RESAffineSpecialization', 'RVChartDisjointUnion', 'RVChartUnionProperties', 'RVNamedTuples', 'RVTaggedCoproduct', 'RVTaggedCoproductProperties', 'RVTaggedCoproductClasses', 'RVGraphComposition', 'RVMeasuredIsomorphisms', 'RVPointProductIsomorphisms', 'RVTaggedComponentIsomorphisms', 'RVDisjointUnionIsomorphisms', 'RVChartRestrictions', 'RVScissorComponents', 'RVTaggedPartitionIsomorphisms', 'RVDisjointInvariants', 'RVDisjointPresentation', 'RVDisjointGrading', 'RVAdmissibleFamilies', 'RVAdmissibleDisjointInvariants', 'RVFamilyDisjointPresentation', 'RESDisjointPresentation', 'RVBoundedDisjointPresentation', 'RVFamilyDisjointGrading', 'RESDisjointGrading', 'RVBoundedDisjointGrading', 'RVOrdinaryScissorComponents', 'RVOrdinaryDisjointInvariants', 'RVOrdinaryFamilyPresentation', 'RVOrdinaryFamilyGrading', 'RESOrdinaryDisjointPresentation', 'RVOrdinaryDisjointPresentation', 'RVDisjointRadiusQuotient', 'RESOrdinaryDisjointGrading', 'RVOrdinaryDisjointGrading', 'RVDisjointPQuotients', 'RESDisjointReduction', 'GammaRVFinitePartitions', 'GammaRVFiniteFamilies', 'FiniteFamilyBijections', 'GammaRVFamilyIsomorphisms', 'GammaRVFamilySharp', 'GammaRVFiniteUnionPresentation', 'GammaRVFiniteUnionGrading', 'GammaRVFiniteUnionOperations', 'GammaBoundedRVPartitions', 'GammaFiniteRVPartitions', 'GammaRestrictedRVFiniteFamilies', 'GammaBoundedRVFiniteUnionPresentation', 'GammaFiniteRVFiniteUnionPresentation', 'GammaBoundedRVFiniteUnionGrading', 'GammaBoundedRVFiniteUnionOperations', 'GammaFiniteRVFiniteUnionGrading', 'GammaFiniteRVFiniteUnionOperations', 'RingPresentationTransport', 'IntrinsicPresentationMaps', 'IntrinsicPresentationGradings', 'CoactionQuotientEquivalence', 'IntrinsicQuotientGradings', 'IntrinsicFiniteGammaAlgebras', 'IntrinsicBalancedTensors', 'IntrinsicBalancedGradings', 'IntrinsicBalancedEvaluations', 'IntrinsicBalancedSpecialClasses', 'IntrinsicBalancedRadiusQuotient', 'IntrinsicBalancedPQuotient', 'RVFiniteOrdinaryCounts', 'RVOrdinaryZeroCount', 'RESOrdinarySurjectivity', 'IntrinsicBoundedNontriviality', 'GammaOrdinaryCharts', 'GammaOrdinaryRing', 'GammaOrdinaryGrading', 'GammaOrdinaryEulerEvaluation', 'GammaOrdinarySharpObjects', 'GammaOrdinarySharpRingMap', 'GammaOrdinarySharpScissors', 'GammaOrdinaryFiniteCharts', 'GammaOrdinaryFiniteRing', 'GammaOrdinaryFiniteGrading', 'GammaOrdinaryFiniteMaps', 'GammaOrdinaryFiniteMapGradings', 'GammaOrdinaryAlgebras', 'GammaOrdinaryRESEvaluation', 'RVOrdinaryBalancedTensor', 'RVOrdinaryBalancedGradings', 'RVOrdinaryIntegerTensor', 'RVOrdinaryBalancedSpecialClasses', 'RVOrdinaryTensorNormalization', 'GammaOrdinaryRadius', 'GammaOrdinaryFinitePartitions', 'GammaOrdinaryFiniteFamilies', 'GammaOrdinaryFamilyIsomorphisms', 'GammaOrdinaryFiniteUnionPresentation', 'GammaOrdinaryFiniteSupportPartitions', 'GammaOrdinaryFiniteUnionGrading', 'GammaOrdinaryFiniteUnionOperations', 'GammaOrdinaryFiniteSupportFamilies', 'RVOrdinaryTensorForget', 'GammaOrdinaryFiniteSupportUnionPresentation', 'RVOrdinaryBoundedTensorForget', 'GammaOrdinaryFamilySharp', 'GammaOrdinaryFiniteSupportUnionGrading', 'GammaOrdinaryFiniteSupportUnionOperations', 'RVOrdinaryNormalizedForget', 'RVVariableMultiplication', 'RVDefinableTupleMaps', 'RVUnaryScaling', 'RVCoefficientShearGraphs', 'RVCoefficientTranslation', 'GammaOrdinaryTranslations', 'RVCoefficientTranslationKernel', 'RVOrdinaryTranslationIdeal', 'RVBoundedCoefficientTranslationKernel', 'RVCoordinateScaling', 'RVCoefficientCoordinateShearGraphs', 'RVCoefficientCoordinateTranslation', 'RVCoefficientCoordinateTranslationKernel', 'RVDefinableGraphExtension', 'RVBoundedCoefficientCoordinateTranslationKernel', 'RVDefinableGraphRES', 'RVCoefficientFunctionTranslationKernel', 'GammaOrdinaryZeroDegreeFinite', 'RVOrdinaryBalancedZeroDegree', 'GammaBoundaryConstancy', 'GammaPartialCellDefinability', 'GammaBoundaryComponents', 'FiniteOrderComponents', 'GammaBoundaryStackBases', 'OrderGapComponents', 'GammaBoundaryStacks', 'GammaGraphPartitionEndpoints', 'GammaBoundaryStackFamily', 'GammaBoundaryStackCoverage', 'GammaBoundaryGapLabels', 'GammaBoundaryStackDisjointness', 'GammaBoundaryStackRefinement', 'GammaCylindricalDecompositionData', 'GammaCylindricalDecompositionExistence', 'GammaCylindricalCellGeometry', 'GammaConstructedCellEuler', 'RVOrdinaryCoefficientTranslationKernel', 'CoactionSurjectiveDescent', 'ApprovedT001Presentation', 'RVT001OrdinaryDescent', 'RVT001MeasuredDescent', 'RVT001OrdinaryNormalization', 'RVT001AlternativeDescent', 'RVT001OrdinaryRanges', 'DefinableGaloisPoints', 'GaloisPointCounts', 'ACFPrimeSpecialization', 'FiniteRelationSeparation', 'FieldPositiveExpressions', 'DefinableBiUniqueRelation', 'ACFFormulaSpecialization', 'GaloisTaggedSum', 'BiUniqueFormula', 'FieldExpressionCongruence', 'FiniteFieldFormulaParameters', 'FieldDefinableRing', 'ACFLargeFiniteParameterField', 'FieldExpressionCounts', 'FiniteFieldPointDiagram', 'FieldAffineNontrivial', 'FieldFiniteCharacters', 'RVResiduePullback', 'FieldAffineTranscendence', 'RVResidueScaledCovers', 'RVResidueFullFibres', 'FieldTaggedFamilies', 'RVResidueFiniteNormalization', 'RVResidueCodes', 'BiUniqueTransport', 'RVResidueChartCodes', 'RVResidueJoinedCovers', 'RVResidueCodeRelations', 'FieldCartesianCharts', 'FieldPointCharts', 'RVResidueIsomorphisms', 'FieldScissorBijection', 'RVResiduePointValues', 'RVResidueCodeIndependence', 'RVResidueRestrictedCodes', 'TupleProductBijections', 'FieldScissorClasses', 'RVResidueProductCodes', 'RVResidueScissors', 'RESResidueTrace', 'RVResidueFibreCodes', 'FieldAffineDecomposition', 'FieldAffineQuotientMap', 'RESPointNonvanishing', 'RVT001RetractionStatements', 'RESOrdinaryResidueTrace', 'FieldAffineLocalizationNontrivial', 'RESAffineSeparation', 'RVT001NormalizedDistinct', 'GammaRationalAffineContinuity', 'GammaContinuousCells', 'Section3GammaAffineInput', 'GammaFiniteFirstMatch', 'GammaContinuousPartitions', 'GammaContinuousStackCells', 'GammaContinuousDecompositionRefinement', 'GammaContinuousDecomposition', 'FieldBoundedProjection', 'FiniteFieldBoundedDiagram', 'RVCoordinatePieceCover', 'FieldBoundedCharacters', 'RVChartCoordinateMap', 'FieldGrowthFiltration', 'RESResidueGrowth', 'RESOrdinaryAdditiveGeneration', 'FieldGrowthSeparation', 'RESHomogeneousGrowth', 'RESAffineNonsurjective', 'Section3PresentationAudit', 'Section3RVCodeBridge', 'Section3RVChartBridge', 'Section3RVFormBridge', 'Section3MeasuredRVChartBridge', 'Section3RVRoundtripBridge', 'Section3RVProductBridge', 'Section3RVRestrictionBridge', 'RVRestrictionInvariants', 'Section3RVClassCuts', 'Section3RVChartCuts', 'Section3RVBasicClasses', 'Section3RVNativeRingMaps', 'Section3RVChartRingMaps', 'Section3RVRingEquivalences', 'Section3GammaCodeBridge', 'Section3GammaChartBridge', 'Section3GammaRelationBridge', 'Section3RVRelationBridge', 'Section3GammaMapBridge', 'Section3GammaRVCodeBridge', 'Section3GammaFamilyBridge', 'Section3RVFamilyBridge', 'FiniteFamilyDomainCongruence', 'Section3GammaCodeFamilyBridge', 'Section3GammaFamilyIsomorphismBridge', 'Section3GammaNativeCodeMaps', 'Section3GammaNativeIsomorphisms', 'Section3GammaRoundtripBridge', 'RVAdmissibleRestrictionInvariants', 'Section3RESClassCuts', 'Section3RESBasicClasses', 'Section3RESNativeRingMaps', 'Section3RESChartCuts', 'Section3RESChartAddMaps', 'ObjectClassAdditiveGeneration', 'Section3RESRingEquivalences', 'Section3GammaFamilyClasses', 'Section3GammaChartAddMaps', 'Section3GammaNativeClassCuts', 'GammaCoordinateIsomorphisms', 'Section3GammaProductBridge', 'Section3GammaBasicClasses', 'Section3GammaNativeRingMaps', 'Section3GammaRingEquivalences', 'Section3FiniteGammaChartBridge', 'FinitePieceValuations', 'Section3FiniteGammaNativeClasses', 'Section3FiniteGammaNativeRingMaps', 'Section3FiniteGammaChartAddMaps', 'Section3FiniteGammaRingEquivalences', 'RingTensorCongruence', 'Section3GammaSharpBridge', 'Section3CoefficientSquares', 'Section3TensorRingEquivalences', 'Section3RVComparisonSquares', 'CompletionTensorMapFormula', 'Section3TensorComparisonSquares', 'Section3CoefficientFunctionBridge', 'Section3CoefficientChartRelations', 'Section3TensorClassTransport', 'Section3CoefficientPairTransport', 'Section3T001Integration', 'Section3LinkedRetractionStatements']


def run(args, path):
    result = subprocess.run(args, cwd=ROOT, text=True, capture_output=True)
    output = result.stdout + result.stderr
    path.write_text(output)
    if result.returncode or 'sorryAx' in output:
        raise SystemExit(output[-6000:])
    return output


def declarations(source):
    # Preserve lines while masking nested Lean comments and string contents.
    # Documentation such as "structure premise ..." is not a declaration.
    code = []
    index = depth = 0
    in_string = False
    while index < len(source):
        char = source[index]
        if depth:
            if source.startswith('/-', index):
                depth += 1
                code.extend('  ')
                index += 2
            elif source.startswith('-/', index):
                depth -= 1
                code.extend('  ')
                index += 2
            else:
                code.append('\n' if char == '\n' else ' ')
                index += 1
        elif in_string:
            if char == '\\' and index + 1 < len(source):
                code.extend('  ')
                index += 2
            else:
                in_string = char != '"'
                code.append('\n' if char == '\n' else ' ')
                index += 1
        elif source.startswith('--', index):
            end = source.find('\n', index)
            if end == -1:
                break
            code.extend(' ' * (end - index))
            index = end
        elif source.startswith('/-', index):
            depth = 1
            code.extend('  ')
            index += 2
        elif char == '"':
            in_string = True
            code.append(' ')
            index += 1
        else:
            code.append(char)
            index += 1
    namespaces = []
    result = []
    for line in ''.join(code).splitlines():
        namespace = re.match(r'namespace ([\w.]+)\s*$', line)
        end = re.match(r'end ([\w.]+)\s*$', line)
        if namespace:
            namespaces.append(namespace[1])
        elif end and namespaces and namespaces[-1] == end[1]:
            namespaces.pop()
        declaration = re.match(r"(?:(?:noncomputable|local) )*(def|abbrev|theorem|inductive|structure|instance) ([\w.']+)", line)
        if declaration:
            name = '.'.join(namespaces + [declaration[2]])
            result.append({'name': name, 'kind': declaration[1]})
    return result


def main():
    RECORD.mkdir(exist_ok=True)
    (RECORD / 'status.json').unlink(missing_ok=True)
    version = subprocess.check_output(['lake', 'env', 'lean', '--version'], cwd=ROOT, text=True).strip()
    if not version.startswith('Lean (version 4.35.0,'):
        raise SystemExit(f'Unexpected Lean toolchain: {version}')
    run(['python3', 'section 2/prepare-reuse.py'], RECORD / 'reuse-preparation.txt')
    run(['lake', 'build', 'DiamondIntegral'], RECORD / 'build.txt')
    sources = [SECTION / (module + '.lean') for module in MODULES]
    exports = [declaration for source in sources for declaration in declarations(source.read_text())]
    names = [declaration['name'] for declaration in exports]
    if not names or len(names) != len(set(names)):
        raise SystemExit('Missing or duplicate audit exports')
    audit = ['import «section 4».Section', 'set_option pp.universes true',
             'set_option pp.fullNames true', 'set_option pp.proofs false',
             'set_option format.width 120']
    audit_names = list(dict.fromkeys(names + list(INPUT_DEFINITIONS)))
    for name in audit_names:
        audit += [f'#print {name}', f'#print axioms {name}']
    audit_path = RECORD / 'Section4Audit.lean'
    audit_path.write_text('\n'.join(audit) + '\n')
    output = run(['lake', 'env', 'lean', str(audit_path.relative_to(ROOT))], RECORD / 'section4-audit.txt')
    found = {}
    for name, raw in re.findall(r"'([^\n]+)' depends on axioms: \[([^\]]*)\]", output):
        raw = re.sub(r'\.\{[^}]*\}', '', raw)
        used = {a.strip() for a in raw.split(',') if a.strip()}
        used = {'Classical.choice' if a == 'choice' else a for a in used}
        if not used <= ALLOWED:
            raise SystemExit(f'Forbidden axioms: {name}: {used - ALLOWED}')
        found[name] = sorted(used)
    for name in re.findall(r"'([^\n]+)' does not depend on any axioms", output):
        found[name] = []
    if set(audit_names) != set(found):
        raise SystemExit(f'Incomplete audit: {sorted(set(audit_names) - set(found))}')
    paths = sources + [SECTION / 'Section.lean', Path(__file__).resolve(), ROOT / 'DiamondIntegral.lean',
                       ROOT / 'lean-toolchain', ROOT / 'lakefile.toml', ROOT / 'lake-manifest.json',
                       ROOT / 'ACCEPTED-CITED-RESULTS.md',
                       RECORD / 'CITED-INPUTS.md',
                       RECORD / 't001-upstream-review.json',
                       RECORD / 'T001-section4-approval.json',
                       RECORD / 'point-nonvanishing.json',
                       RECORD / 'affine-nonsurjectivity.json',
                       RECORD / 'final-section3-audit.json',
                       ROOT / 'section 3/TensorRingKernelPresentations.lean',
                       ROOT / 'section 3/TensorRingDescent.lean',
                       ROOT / 'section 3/TensorCoefficientRelations.lean',
                       ROOT / 'section 3/MeasuredTensorCoefficientRelations.lean',
                       ROOT / 'section 3/reuse/integration-manifest.json',
                       SECTION / 'reference/T001-approved-upstream.tex',
                       ROOT / 'section 2/CitedGammaLinearity.lean',
                       ROOT / 'section 2/AtomicBaseChange.lean',
                       ROOT / 'section 2/Conventions.lean',
                       ROOT / 'section 2/reuse/manifest.json',
                       ROOT / 'section 2/reuse/open-disc-radius.patch',
                       ROOT / 'section 2/reference/diamond_integral_revision_annotated.tex']
    record = {
        'status': 'PASS', 'scope': 'Project entry-point build; complete §4 declaration types and logical axiom audit.',
        'section_completion': 'COMPLETE_WITH_FINALIZED_SECTION3_TRANSPORT',
        'finalized_section3_statement_audit': 'PASS',
        'end_to_end_section3_presentation_transport': 'PASS_INSTANTIATED',
        'remaining_section4_main_text_obligations': [],
        'numbered_results_complete': ['Proposition 4.7', 'Proposition 4.15'],
        'numbered_results_basis': 'Linked directly to finalized Section 3 tensor kernel proofs at 37c8361 through actual factor/tensor/target ring equivalences, commuting comparison squares and elementary-pair ideal transport. No T001 interface is a theorem input. Original-base saturation, ACVF00, smallness, nontrivial Gamma and the accepted rational-affine Gamma background remain explicit.',
        'numbered_statements_linked_to_finalized_section3': {
            'Proposition 4.7': 'DiamondIntegral.Section4.Section3LinkedRetractionStatements.proposition_4_7',
            'Proposition 4.15': 'DiamondIntegral.Section4.Section3LinkedRetractionStatements.proposition_4_15',
        },
        'local_proof_completion': {
            'actual_degree_one_point_nonvanishing': 'DiamondIntegral.Section4.RESPointNonvanishing.point_ne_zero_acvf00',
            'actual_affine_point_separation': 'DiamondIntegral.Section4.RESAffineSeparation.comparison_point_ne_one_acvf00',
            'continuous_cell_decomposition': 'DiamondIntegral.Section4.GammaContinuousDecomposition.exists_decomposition',
            'continuous_cell_euler_formula': 'DiamondIntegral.Section4.GammaContinuousDecomposition.geometric_sum',
            'actual_affine_comparison_nonsurjectivity': 'DiamondIntegral.Section4.RESAffineNonsurjective.remark_4_4',
        }, 'lean': version,
        'upstream_project_dependencies': {'T001': json.loads((RECORD / 't001-upstream-review.json').read_text())},
        'semantic_boundary': 'Section 4 corrected main-text proofs are complete and linked to finalized Section 3. Section3T001Integration constructs both ordinary and measured T001 interfaces from actual upstream kernel and surjectivity proofs through proved categorical-to-chart ring equivalences, scalar/comparison squares and elementary coefficient-pair transport. Section3LinkedRetractionStatements proves all clauses of Propositions 4.7 and 4.15 without T001 inputs. General rational-affine Gamma normal form remains explicit accepted QE background; the integral-affine contraction classification is not substituted for it. The bounded construction uses the full ordinary presentation, with no bounded tensor kernel or injectivity premise. Nonnegative radius generators retain original-base definable RV lifts; arbitrary definable Gamma values are not asserted to have lifts. Original-base parameters, finite tags, object degrees, partial forms and full RV preimages are retained throughout. Continuous cell decomposition, Euler descent, actual point nonvanishing and affine-localization comparison nonsurjectivity are proved locally. No HK result is an input. The already authorized later external inputs in Section 3 remain within their documented scope; coefficient-monicity R-Y input is not needed for Section 4 Euler descent.',
        'public_declarations': exports, 'declarations': {name: found[name] for name in names},
        'cited_input_definitions': {name: {'source': path, 'axioms': found[name]}
                                    for name, path in INPUT_DEFINITIONS.items()},
        'sources': {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths},
    }
    (RECORD / 'status.json').write_text(json.dumps(record, indent=2) + '\n')
    theorems = sum(declaration['kind'] == 'theorem' for declaration in exports)
    print(f'PASS: project entry point; {len(names)} declarations ({theorems} theorems); full types and permitted-axiom audit.')


if __name__ == '__main__':
    main()
