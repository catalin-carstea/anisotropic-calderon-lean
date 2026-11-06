import Mathlib.Tactic.ApplyWith
import Calderon.SubmoduleRealNaturalStructureData
import Calderon.RealHarmonicInheritedStructureData
import Calderon.RealNormedGroupProjectionData
import Calderon.NativeStrongDirichletInverseForcingComposition
import Calderon.NativeStrongDirichletInverseForcingCompositionLaws
import Calderon.NativeSobolevStageStructure
import Calderon.SequenceLpInheritedStructureData
import Calderon.SequenceLpNaturalStructureData
import Calderon.InheritedNormedStructureData
import Calderon.LpInheritedStructureData
import Calderon.NativeHighSmoothMultiplierForcing
import Calderon.ActualReferenceInverseOneLowerCoherence
import Calderon.ActualReferenceSmoothMultiplierStrongDefect
import Calderon.ActualReferenceInvertibleStrongWeakCoherence
import Calderon.NativeHighStrongSobolevTopology

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
ACTUAL-HIGH-SMOOTH-MULTIPLIER-GAIN-EXPANSION-v001.md. SAME correction gains one finite native order. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeHarmonicLiftCompletion
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

attribute [local irreducible] harmonicSphereSubspace

theorem strong_real_nontriviallyNormedField_normedField_eq :
    (Real.denselyNormedField.toNontriviallyNormedField).toNormedField = Real.normedField := rfl

theorem real_normedCommRing_semiring_eq_natural :
    Real.normedCommRing.toNormedRing.toRing.toSemiring = Real.semiring := rfl

theorem strong_submodule_seminormedAddCommGroup_topologicalSpace_eq
    (V : Type*) [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    (s : Submodule ℝ V) :
    (Submodule.seminormedAddCommGroup s).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace s) := rfl

theorem strong_submodule_seminormedAddCommGroup_addCommMonoid_eq
    (V : Type*) [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    (s : Submodule ℝ V) :
    (Submodule.seminormedAddCommGroup s).toAddCommGroup.toAddCommMonoid =
      Submodule.addCommMonoid s := rfl

theorem strong_submodule_normedSpace_module_eq
    (V : Type*) [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    (s : Submodule ℝ V) :
    (Submodule.normedSpace (𝕜 := ℝ) s).toModule = Submodule.module s := rfl

theorem strong_submodule_normedAddCommGroup_seminormedAddCommGroup_eq
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    (s : Submodule ℝ V) :
    (Submodule.normedAddCommGroup s).toSeminormedAddCommGroup =
      Submodule.seminormedAddCommGroup s := rfl

theorem strong_lp_normedAddCommGroup_addCommMonoid_eq
    (A E : Type*) [MeasurableSpace A] [NormedAddCommGroup E]
    (p : ENNReal) [Fact (1 ≤ p)] (mu : Measure A) :
    (Lp.instNormedAddCommGroup (E := E) (p := p) (μ := mu)).toAddCommGroup.toAddCommMonoid =
      (inferInstance : AddCommMonoid (Lp E p mu)) := rfl

theorem strong_lp_normedSpace_module_eq
    (A E : Type*) [MeasurableSpace A] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : ENNReal) [Fact (1 ≤ p)] (mu : Measure A) :
    (Lp.instNormedSpace (𝕜 := ℝ) (E := E) (p := p) (μ := mu)).toModule =
      (inferInstance : Module ℝ (Lp E p mu)) := rfl

attribute [local irreducible] referenceCoordinateForcingPrincipalJets referenceCoordinateForcingDriftJets
  referenceStrongDriftFamily referenceHarmonicLiftFamily harmonicLiftCompletion
  referenceSmoothMultiplierStrongDefectFamily referenceSmoothMultiplierCommutatorForcingFamily
  referenceWeakHalfLiftFamily nativeBulkMultiplierCommutatorForcingL nativeHighBulkMultiplierCommutatorForcingL
  nativeStrongDirichletInclusionL nativeStrongDirichletInverseInclusionL
  nativeStrongDirichletInverseForcingCompositionL


def referenceHighSmoothMultiplierCommutatorForcingFamily (hcalc : FixedSobolevCalculus)
    (Q : SmoothCoefficientJets 3) (p : ℝ × (R3 × ℝ)) :
    BallSobolev 2 →L[ℝ] BallSobolev 1 :=
  nativeHighBulkMultiplierCommutatorForcingL hcalc
    (referenceCoordinateForcingPrincipalJets g L y0 Φ B ε C ρ H a w hData p)
    (referenceCoordinateForcingDriftJets g L y0 Φ B ε C ρ H a w hData p) Q

attribute [local instance] highStrongNativeH3Group

attribute [local instance] highStrongNativeH3Space

def referenceHighSmoothMultiplierStrongDefectFunction
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (Q : SmoothCoefficientJets 3) (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (3/2 : ℝ) → BallSobolev 3 := fun f =>
  nativeStrongDirichletInverseInclusionL 1
    (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 p.1 p.2)
    (referenceHighSmoothMultiplierCommutatorForcingFamily
      g L y0 Φ B ε C ρ H a w hData hcalc Q p
      ((referenceHarmonicLiftFamily
        g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2) (harmonicLiftCompletion hF f)))

lemma referenceHighSmoothMultiplierStrongDefectFunction_apply
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (Q : SmoothCoefficientJets 3) (p : ℝ × (R3 × ℝ))
    (f : SphereSobolev (3/2 : ℝ)) :
    referenceHighSmoothMultiplierStrongDefectFunction g L y0 Φ B ε C ρ H a w hData hcalc hF Q p f =
      nativeStrongDirichletInverseInclusionL 1
        (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 p.1 p.2)
        (referenceHighSmoothMultiplierCommutatorForcingFamily
          g L y0 Φ B ε C ρ H a w hData hcalc Q p
          ((referenceHarmonicLiftFamily
            g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2) (harmonicLiftCompletion hF f))) := by
  rfl


lemma referenceHighSmoothMultiplierStrongDefectFunction_map_add
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (Q : SmoothCoefficientJets 3) (p : ℝ × (R3 × ℝ))
    (f g' : SphereSobolev (3/2 : ℝ)) :
    referenceHighSmoothMultiplierStrongDefectFunction g L y0 Φ B ε C ρ H a w hData hcalc hF Q p (f+g') =
      referenceHighSmoothMultiplierStrongDefectFunction g L y0 Φ B ε C ρ H a w hData hcalc hF Q p f + referenceHighSmoothMultiplierStrongDefectFunction g L y0 Φ B ε C ρ H a w hData hcalc hF Q p g' := by
  have hHarmonicModule (k : ℕ) :
      (Submodule.normedSpace (𝕜 := ℝ) (harmonicSphereSubspace k)).toModule =
        (harmonicSphereSubspace k).module := rfl
  have hActualHarmonicModule (k : ℕ) :
      letI : NormedSpace ℝ ℝ :=
        (RCLike.toInnerProductSpaceReal (𝕜 := ℝ)).toNormedSpace
      (Submodule.normedSpace (𝕜 := ℝ) (R := ℝ) (harmonicSphereSubspace k)).toModule =
        Submodule.module (harmonicSphereSubspace k) := by
    rfl
  let N : BallSobolev 2 →L[ℝ] BallSobolev 1 :=
    referenceHighSmoothMultiplierCommutatorForcingFamily g L y0 Φ B ε C ρ H a w hData hcalc Q p
  let U : SphereSobolev (3/2 : ℝ) →L[ℝ] BallSobolev 2 :=
    (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).comp
      (harmonicLiftCompletion hF)
  let A := referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 p.1 p.2
  let nativeMap := nativeStrongDirichletInverseForcingCompositionL
    (X := SphereSobolev (3/2 : ℝ)) (Y := BallSobolev 2) 1 A N U
  let nativeFun := referenceHighSmoothMultiplierStrongDefectFunction g L y0 Φ B ε C ρ H a w hData hcalc hF Q p
  have hActualGraph (x : SphereSobolev (3/2 : ℝ)) :
      nativeStrongDirichletInverseForcingCompositionL
        (X := SphereSobolev (3/2 : ℝ)) (Y := BallSobolev 2) 1 A N U x = nativeFun x := by
    simpa only [nativeMap, nativeStrongDirichletInverseForcingCompositionL,
      ContinuousLinearMap.comp_apply, nativeFun, N, U, A] using
      (referenceHighSmoothMultiplierStrongDefectFunction_apply g L y0 Φ B ε C ρ H a w hData hcalc hF Q p x).symm
  have hNative := nativeStrongDirichletInverseForcingCompositionL_map_add 1 A N U f g'
  simp only [hActualGraph] at hNative
  change nativeFun (f+g') = nativeFun f+nativeFun g'
  set_option backward.dsimp.proofs true in
    try simp (config := { instances := true }) only
      [real_seminormedRing_seminormedAddCommGroup_eq,real_ring_semiring_eq,real_normedCommRing_semiring_eq_natural,
      lp_two_normedAddCommGroup_addCommMonoid_eq_natural,
      submodule_normedAddCommGroup_seminormedAddCommGroup_eq_independent,
      submodule_seminormedAddCommGroup_topologicalSpace_eq_subtype,
      submodule_seminormedAddCommGroup_addCommMonoid_eq_natural,
      real_semifield_semiring_eq_natural,real_seminormedRing_addCommGroup_eq_natural,
      real_seminormedRing_pseudoMetricSpace_eq_natural,
      real_normedAddCommGroup_addGroup_eq_natural,real_normedAddCommGroup_pseudoMetricSpace_eq_natural,
      nativeSobolevSucc_normedAddCommGroup_eq_stage,nativeSobolevSucc_normedSpace_eq_stage,
      strong_real_nontriviallyNormedField_normedField_eq,harmonicSphereSubspace_normedSpace_module_eq_projected,
      hActualHarmonicModule,hHarmonicModule,
      sequenceLp_normedAddCommGroup_addCommMonoid_eq_natural,
      sequenceLp_normedSpace_module_eq_natural,
      strong_submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
      strong_submodule_seminormedAddCommGroup_topologicalSpace_eq,
      strong_submodule_seminormedAddCommGroup_addCommMonoid_eq,strong_submodule_normedSpace_module_eq,
      strong_lp_normedAddCommGroup_addCommMonoid_eq,strong_lp_normedSpace_module_eq,
      highStrongNativeH3Group,highStrongNativeH3Space,Nat.reduceAdd,SphereSobolev] at ⊢
  dbg_trace "STRONG_ADD_TARGET_NORMALIZATION_RETURNED"
  all_goals
    set_option backward.dsimp.proofs true in
      try simp (config := { instances := true }) only
        [real_seminormedRing_seminormedAddCommGroup_eq,real_ring_semiring_eq,real_normedCommRing_semiring_eq_natural,
        lp_two_normedAddCommGroup_addCommMonoid_eq_natural,
        submodule_normedAddCommGroup_seminormedAddCommGroup_eq_independent,
        submodule_seminormedAddCommGroup_topologicalSpace_eq_subtype,
        submodule_seminormedAddCommGroup_addCommMonoid_eq_natural,
        real_semifield_semiring_eq_natural,real_seminormedRing_addCommGroup_eq_natural,
        real_seminormedRing_pseudoMetricSpace_eq_natural,
        real_normedAddCommGroup_addGroup_eq_natural,real_normedAddCommGroup_pseudoMetricSpace_eq_natural,
        nativeSobolevSucc_normedAddCommGroup_eq_stage,nativeSobolevSucc_normedSpace_eq_stage,
        strong_real_nontriviallyNormedField_normedField_eq,harmonicSphereSubspace_normedSpace_module_eq_projected,
        hActualHarmonicModule,hHarmonicModule,
        sequenceLp_normedAddCommGroup_addCommMonoid_eq_natural,
        sequenceLp_normedSpace_module_eq_natural,
        strong_submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
        strong_submodule_seminormedAddCommGroup_topologicalSpace_eq,
        strong_submodule_seminormedAddCommGroup_addCommMonoid_eq,strong_submodule_normedSpace_module_eq,
        strong_lp_normedAddCommGroup_addCommMonoid_eq,strong_lp_normedSpace_module_eq,
        highStrongNativeH3Group,highStrongNativeH3Space,Nat.reduceAdd,SphereSobolev] at hNative
    dbg_trace "STRONG_ADD_NATIVE_NORMALIZATION_RETURNED"
    dbg_trace "STRONG_ADD_OPERATION_CHAIN_ENTERED"
    refine Eq.trans ?_ (Eq.trans hNative ?_)
    · dbg_trace "STRONG_INPUT_ADD_BRIDGE_ENTERED"
      apply congrArg nativeFun
      have hInputMonoid := sequenceLp_normedAddCommGroup_addCommMonoid_eq_natural
        (fun k : ℕ => harmonicSphereSubspace k) (2 : ENNReal)
      dbg_trace "STRONG_INPUT_ADD_MONOID_CERTIFICATE_READY"
      have hInputOp := congrArg
        (fun M : AddCommMonoid (SphereSobolev (3/2 : ℝ)) => M.toAddMonoid.toAdd)
        hInputMonoid
      dbg_trace "STRONG_INPUT_ADD_OPERATION_CERTIFICATE_READY"
      have hInputPoint := congrArg
        (fun op : Add (SphereSobolev (3/2 : ℝ)) => @Add.add _ op f g') hInputOp
      dbg_trace "STRONG_INPUT_ADD_POINT_CERTIFICATE_READY"
      exact hInputPoint.symm
    · dbg_trace "STRONG_OUTPUT_ADD_BRIDGE_ENTERED"
      have hOutputGroup := nativeSobolevSucc_normedAddCommGroup_eq_stage 2
      dbg_trace "STRONG_OUTPUT_ADD_GROUP_CERTIFICATE_READY"
      have hOutputOp := congrArg
        (fun G : NormedAddCommGroup (BallSobolev 3) =>
          G.toAddCommGroup.toAddCommMonoid.toAddMonoid.toAdd) hOutputGroup
      dbg_trace "STRONG_OUTPUT_ADD_OPERATION_CERTIFICATE_READY"
      have hOutputPoint := congrArg
        (fun op : Add (BallSobolev 3) => @Add.add _ op (nativeFun f) (nativeFun g'))
        hOutputOp
      dbg_trace "STRONG_OUTPUT_ADD_POINT_CERTIFICATE_READY"
      refine TauCeti.Wkp.ext 3 ?_
      dbg_trace "STRONG_OUTPUT_ADD_VALUE_GOAL_ENTERED"
      simp only [TauCeti.Wkp.value_add]


lemma referenceHighSmoothMultiplierStrongDefectFunction_map_smul
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (Q : SmoothCoefficientJets 3) (p : ℝ × (R3 × ℝ))
    (c : ℝ) (f : SphereSobolev (3/2 : ℝ)) :
    referenceHighSmoothMultiplierStrongDefectFunction g L y0 Φ B ε C ρ H a w hData hcalc hF Q p (c • f) =
      c • referenceHighSmoothMultiplierStrongDefectFunction g L y0 Φ B ε C ρ H a w hData hcalc hF Q p f := by
  have hHarmonicModule (k : ℕ) :
      (Submodule.normedSpace (𝕜 := ℝ) (harmonicSphereSubspace k)).toModule =
        (harmonicSphereSubspace k).module := rfl
  have hActualHarmonicModule (k : ℕ) :
      letI : NormedSpace ℝ ℝ :=
        (RCLike.toInnerProductSpaceReal (𝕜 := ℝ)).toNormedSpace
      (Submodule.normedSpace (𝕜 := ℝ) (R := ℝ) (harmonicSphereSubspace k)).toModule =
        Submodule.module (harmonicSphereSubspace k) := by
    rfl
  let N : BallSobolev 2 →L[ℝ] BallSobolev 1 :=
    referenceHighSmoothMultiplierCommutatorForcingFamily g L y0 Φ B ε C ρ H a w hData hcalc Q p
  let U : SphereSobolev (3/2 : ℝ) →L[ℝ] BallSobolev 2 :=
    (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).comp
      (harmonicLiftCompletion hF)
  let A := referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 p.1 p.2
  let nativeMap := nativeStrongDirichletInverseForcingCompositionL
    (X := SphereSobolev (3/2 : ℝ)) (Y := BallSobolev 2) 1 A N U
  let nativeFun := referenceHighSmoothMultiplierStrongDefectFunction g L y0 Φ B ε C ρ H a w hData hcalc hF Q p
  have hActualGraph (x : SphereSobolev (3/2 : ℝ)) :
      nativeStrongDirichletInverseForcingCompositionL
        (X := SphereSobolev (3/2 : ℝ)) (Y := BallSobolev 2) 1 A N U x = nativeFun x := by
    simpa only [nativeMap, nativeStrongDirichletInverseForcingCompositionL,
      ContinuousLinearMap.comp_apply, nativeFun, N, U, A] using
      (referenceHighSmoothMultiplierStrongDefectFunction_apply g L y0 Φ B ε C ρ H a w hData hcalc hF Q p x).symm
  have hNative := nativeStrongDirichletInverseForcingCompositionL_map_smul 1 A N U c f
  simp only [hActualGraph] at hNative
  change nativeFun (c • f) = c • nativeFun f
  try simp (config := { instances := true }) only
    [real_seminormedRing_seminormedAddCommGroup_eq,real_ring_semiring_eq,real_normedCommRing_semiring_eq_natural,
    lp_two_normedAddCommGroup_addCommMonoid_eq_natural,
    submodule_normedAddCommGroup_seminormedAddCommGroup_eq_independent,
    submodule_seminormedAddCommGroup_topologicalSpace_eq_subtype,
    submodule_seminormedAddCommGroup_addCommMonoid_eq_natural,
    real_semifield_semiring_eq_natural,real_seminormedRing_addCommGroup_eq_natural,
    real_seminormedRing_pseudoMetricSpace_eq_natural,
    real_normedAddCommGroup_addGroup_eq_natural,real_normedAddCommGroup_pseudoMetricSpace_eq_natural,
    nativeSobolevSucc_normedAddCommGroup_eq_stage,nativeSobolevSucc_normedSpace_eq_stage,
    strong_real_nontriviallyNormedField_normedField_eq,harmonicSphereSubspace_normedSpace_module_eq_projected,
    hActualHarmonicModule,hHarmonicModule,
    sequenceLp_normedAddCommGroup_addCommMonoid_eq_natural,
    sequenceLp_normedSpace_module_eq_natural,
    strong_submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
    strong_submodule_seminormedAddCommGroup_topologicalSpace_eq,
    strong_submodule_seminormedAddCommGroup_addCommMonoid_eq,strong_submodule_normedSpace_module_eq,
    strong_lp_normedAddCommGroup_addCommMonoid_eq,strong_lp_normedSpace_module_eq,
    highStrongNativeH3Group,highStrongNativeH3Space,Nat.reduceAdd,SphereSobolev] at ⊢
  dbg_trace "STRONG_SMUL_TARGET_NORMALIZATION_RETURNED"
  all_goals
    try simp (config := { instances := true }) only
      [real_seminormedRing_seminormedAddCommGroup_eq,real_ring_semiring_eq,real_normedCommRing_semiring_eq_natural,
      lp_two_normedAddCommGroup_addCommMonoid_eq_natural,
      submodule_normedAddCommGroup_seminormedAddCommGroup_eq_independent,
      submodule_seminormedAddCommGroup_topologicalSpace_eq_subtype,
      submodule_seminormedAddCommGroup_addCommMonoid_eq_natural,
      real_semifield_semiring_eq_natural,real_seminormedRing_addCommGroup_eq_natural,
      real_seminormedRing_pseudoMetricSpace_eq_natural,
      real_normedAddCommGroup_addGroup_eq_natural,real_normedAddCommGroup_pseudoMetricSpace_eq_natural,
      nativeSobolevSucc_normedAddCommGroup_eq_stage,nativeSobolevSucc_normedSpace_eq_stage,
      strong_real_nontriviallyNormedField_normedField_eq,harmonicSphereSubspace_normedSpace_module_eq_projected,
      hActualHarmonicModule,hHarmonicModule,
      sequenceLp_normedAddCommGroup_addCommMonoid_eq_natural,
      sequenceLp_normedSpace_module_eq_natural,
      strong_submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
      strong_submodule_seminormedAddCommGroup_topologicalSpace_eq,
      strong_submodule_seminormedAddCommGroup_addCommMonoid_eq,strong_submodule_normedSpace_module_eq,
      strong_lp_normedAddCommGroup_addCommMonoid_eq,strong_lp_normedSpace_module_eq,
      highStrongNativeH3Group,highStrongNativeH3Space,Nat.reduceAdd,SphereSobolev] at hNative
    dbg_trace "STRONG_SMUL_NATIVE_NORMALIZATION_RETURNED"
    refine Eq.trans ?_ (Eq.trans hNative ?_)
    · dbg_trace "STRONG_INPUT_SMUL_BRIDGE_ENTERED"
      apply congrArg nativeFun
      have hInputModule := sequenceLp_normedSpace_module_eq_natural
        (fun k : ℕ => harmonicSphereSubspace k) (2 : ENNReal)
      dbg_trace "STRONG_INPUT_SMUL_MODULE_CERTIFICATE_READY"
      have hInputDistrib := congrArg
        (@Module.toDistribMulAction ℝ (SphereSobolev (3/2 : ℝ)) _ _) hInputModule
      dbg_trace "STRONG_INPUT_SMUL_DISTRIB_CERTIFICATE_READY"
      have hInputAction := congrArg
        (@DistribMulAction.toMulAction ℝ (SphereSobolev (3/2 : ℝ)) _ _) hInputDistrib
      dbg_trace "STRONG_INPUT_SMUL_ACTION_CERTIFICATE_READY"
      have hInputSemigroup := congrArg
        (@MulAction.toSemigroupAction ℝ (SphereSobolev (3/2 : ℝ)) _) hInputAction
      dbg_trace "STRONG_INPUT_SMUL_SEMIGROUP_CERTIFICATE_READY"
      have hInputOp := congrArg
        (@SemigroupAction.toSMul ℝ (SphereSobolev (3/2 : ℝ)) _) hInputSemigroup
      dbg_trace "STRONG_INPUT_SMUL_OPERATION_CERTIFICATE_READY"
      have hInputPoint := congrArg
        (fun op : SMul ℝ (SphereSobolev (3/2 : ℝ)) => @SMul.smul ℝ _ op c f)
        hInputOp
      dbg_trace "STRONG_INPUT_SMUL_POINT_CERTIFICATE_READY"
      exact hInputPoint.symm
    · dbg_trace "STRONG_OUTPUT_SMUL_BRIDGE_ENTERED"
      refine TauCeti.Wkp.ext 3 ?_
      dbg_trace "STRONG_OUTPUT_SMUL_VALUE_GOAL_ENTERED"
      simp only [TauCeti.Wkp.value_smul, RingHom.id_apply]


lemma continuous_referenceHighSmoothMultiplierStrongDefectFunction
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (Q : SmoothCoefficientJets 3) (p : ℝ × (R3 × ℝ)) :
    Continuous (referenceHighSmoothMultiplierStrongDefectFunction g L y0 Φ B ε C ρ H a w hData hcalc hF Q p) := by
  have hHarmonicModule (k : ℕ) :
      (Submodule.normedSpace (𝕜 := ℝ) (harmonicSphereSubspace k)).toModule =
        (harmonicSphereSubspace k).module := rfl
  have hActualHarmonicModule (k : ℕ) :
      letI : NormedSpace ℝ ℝ :=
        (RCLike.toInnerProductSpaceReal (𝕜 := ℝ)).toNormedSpace
      (Submodule.normedSpace (𝕜 := ℝ) (R := ℝ) (harmonicSphereSubspace k)).toModule =
        Submodule.module (harmonicSphereSubspace k) := by
    rfl
  let N : BallSobolev 2 →L[ℝ] BallSobolev 1 :=
    referenceHighSmoothMultiplierCommutatorForcingFamily g L y0 Φ B ε C ρ H a w hData hcalc Q p
  let U : SphereSobolev (3/2 : ℝ) →L[ℝ] BallSobolev 2 :=
    (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).comp
      (harmonicLiftCompletion hF)
  let A := referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 p.1 p.2
  let nativeMap := nativeStrongDirichletInverseForcingCompositionL
    (X := SphereSobolev (3/2 : ℝ)) (Y := BallSobolev 2) 1 A N U
  let originalNativeFun := fun f : SphereSobolev (3/2 : ℝ) => nativeMap f
  let nativeFun := referenceHighSmoothMultiplierStrongDefectFunction g L y0 Φ B ε C ρ H a w hData hcalc hF Q p
  have hNormalizedPrimitiveGraph (f : SphereSobolev (3/2 : ℝ)) :
      nativeFun f = originalNativeFun f := by
    simpa only [nativeMap, nativeStrongDirichletInverseForcingCompositionL,
      ContinuousLinearMap.comp_apply, originalNativeFun, nativeFun, N, U, A] using
      (referenceHighSmoothMultiplierStrongDefectFunction_apply g L y0 Φ B ε C ρ H a w hData hcalc hF Q p f)
  have hNative := continuous_nativeStrongDirichletInverseForcingCompositionL 1 A N U
  change Continuous nativeFun
  try simp (config := { instances := true }) only
    [real_seminormedRing_seminormedAddCommGroup_eq,real_ring_semiring_eq,real_normedCommRing_semiring_eq_natural,
    lp_two_normedAddCommGroup_addCommMonoid_eq_natural,
    submodule_normedAddCommGroup_seminormedAddCommGroup_eq_independent,
    submodule_seminormedAddCommGroup_topologicalSpace_eq_subtype,
    submodule_seminormedAddCommGroup_addCommMonoid_eq_natural,
    real_semifield_semiring_eq_natural,real_seminormedRing_addCommGroup_eq_natural,
    real_seminormedRing_pseudoMetricSpace_eq_natural,
    real_normedAddCommGroup_addGroup_eq_natural,real_normedAddCommGroup_pseudoMetricSpace_eq_natural,
    nativeSobolevSucc_normedAddCommGroup_eq_stage,nativeSobolevSucc_normedSpace_eq_stage,
    strong_real_nontriviallyNormedField_normedField_eq,harmonicSphereSubspace_normedSpace_module_eq_projected,
    hActualHarmonicModule,hHarmonicModule,
    sequenceLp_normedAddCommGroup_addCommMonoid_eq_natural,
    sequenceLp_normedSpace_module_eq_natural,
    strong_submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
    strong_submodule_seminormedAddCommGroup_topologicalSpace_eq,
    strong_submodule_seminormedAddCommGroup_addCommMonoid_eq,strong_submodule_normedSpace_module_eq,
    strong_lp_normedAddCommGroup_addCommMonoid_eq,strong_lp_normedSpace_module_eq,
    highStrongNativeH3Group,highStrongNativeH3Space,Nat.reduceAdd,SphereSobolev] at ⊢
  dbg_trace "STRONG_CONT_TARGET_NORMALIZATION_RETURNED"
  all_goals
    try simp (config := { instances := true }) only
      [real_seminormedRing_seminormedAddCommGroup_eq,real_ring_semiring_eq,real_normedCommRing_semiring_eq_natural,
      lp_two_normedAddCommGroup_addCommMonoid_eq_natural,
      submodule_normedAddCommGroup_seminormedAddCommGroup_eq_independent,
      submodule_seminormedAddCommGroup_topologicalSpace_eq_subtype,
      submodule_seminormedAddCommGroup_addCommMonoid_eq_natural,
      real_semifield_semiring_eq_natural,real_seminormedRing_addCommGroup_eq_natural,
      real_seminormedRing_pseudoMetricSpace_eq_natural,
      real_normedAddCommGroup_addGroup_eq_natural,real_normedAddCommGroup_pseudoMetricSpace_eq_natural,
      nativeSobolevSucc_normedAddCommGroup_eq_stage,nativeSobolevSucc_normedSpace_eq_stage,
      strong_real_nontriviallyNormedField_normedField_eq,harmonicSphereSubspace_normedSpace_module_eq_projected,
      hActualHarmonicModule,hHarmonicModule,
      sequenceLp_normedAddCommGroup_addCommMonoid_eq_natural,
      sequenceLp_normedSpace_module_eq_natural,
      strong_submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
      strong_submodule_seminormedAddCommGroup_topologicalSpace_eq,
      strong_submodule_seminormedAddCommGroup_addCommMonoid_eq,strong_submodule_normedSpace_module_eq,
      strong_lp_normedAddCommGroup_addCommMonoid_eq,strong_lp_normedSpace_module_eq,
      highStrongNativeH3Group,highStrongNativeH3Space,Nat.reduceAdd,SphereSobolev] at hNative
    dbg_trace "STRONG_CONT_NATIVE_NORMALIZATION_RETURNED"
    have hCanonicalNative :
        @Continuous (SphereSobolev (3/2 : ℝ)) (BallSobolev 3)
          nativeHighStrongInputTopology nativeHighStrongOutputTopology originalNativeFun := by
      dbg_trace "STRONG_ADAPTER_CANONICAL_NATIVE_MATCH_ENTER"
      simpa (config := { instances := true }) only
        [nativeHighStrongInputTopology,
          nativeHighStrongOutputTopology,
          inferInstance,
          originalNativeFun,
          real_seminormedRing_seminormedAddCommGroup_eq,
          real_ring_semiring_eq,
          real_normedCommRing_semiring_eq_natural,
          lp_two_normedAddCommGroup_addCommMonoid_eq_natural,
          submodule_normedAddCommGroup_seminormedAddCommGroup_eq_independent,
          submodule_seminormedAddCommGroup_topologicalSpace_eq_subtype,
          submodule_seminormedAddCommGroup_addCommMonoid_eq_natural,
          real_semifield_semiring_eq_natural,
          real_seminormedRing_addCommGroup_eq_natural,
          real_seminormedRing_pseudoMetricSpace_eq_natural,
          real_normedAddCommGroup_addGroup_eq_natural,
          real_normedAddCommGroup_pseudoMetricSpace_eq_natural,
          nativeSobolevSucc_normedAddCommGroup_eq_stage,
          nativeSobolevSucc_normedSpace_eq_stage,
          strong_real_nontriviallyNormedField_normedField_eq,
          harmonicSphereSubspace_normedSpace_module_eq_projected,
          hActualHarmonicModule,
          hHarmonicModule,
          sequenceLp_normedAddCommGroup_addCommMonoid_eq_natural,
          sequenceLp_normedSpace_module_eq_natural,
          strong_submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
          strong_submodule_seminormedAddCommGroup_topologicalSpace_eq,
          strong_submodule_seminormedAddCommGroup_addCommMonoid_eq,
          strong_submodule_normedSpace_module_eq,
          strong_lp_normedAddCommGroup_addCommMonoid_eq,
          strong_lp_normedSpace_module_eq,
          highStrongNativeH3Group,
          highStrongNativeH3Space,
          Nat.reduceAdd,
          SphereSobolev] using hNative
    dbg_trace "STRONG_ADAPTER_CANONICAL_NATIVE_MATCH_RETURNED"
    have hOriginalH3 :=
      continuous_highStrongNativeH3_of_continuous_native originalNativeFun hCanonicalNative
    dbg_trace "STRONG_ADAPTER_CHECKED_SAME_FUNCTION_TRANSPORT_RETURNED"
    have hSameFunction : nativeFun = originalNativeFun := by
      funext f
      exact hNormalizedPrimitiveGraph f
    dbg_trace "STRONG_ADAPTER_EXISTING_FUNCTION_GRAPH_RETURNED"
    have hNormalizedH3 :
        @Continuous (SphereSobolev (3/2 : ℝ)) (BallSobolev 3)
          nativeHighStrongInputTopology
          highStrongNativeH3Group.toSeminormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
          nativeFun := by
      exact Eq.mpr (congrArg
        (fun F : SphereSobolev (3/2 : ℝ) → BallSobolev 3 =>
          @Continuous (SphereSobolev (3/2 : ℝ)) (BallSobolev 3)
            nativeHighStrongInputTopology
            highStrongNativeH3Group.toSeminormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace F)
        hSameFunction) hOriginalH3
    dbg_trace "STRONG_ADAPTER_PROVED_GRAPH_TRANSPORT_RETURNED"
    dbg_trace "STRONG_ADAPTER_ORIGINAL_NATIVE_TARGET_MATCH_ENTER"
    simpa (config := { instances := true }) only
      [nativeHighStrongInputTopology,
        inferInstance,
        real_seminormedRing_seminormedAddCommGroup_eq,
        real_ring_semiring_eq,
        real_normedCommRing_semiring_eq_natural,
        lp_two_normedAddCommGroup_addCommMonoid_eq_natural,
        submodule_normedAddCommGroup_seminormedAddCommGroup_eq_independent,
        submodule_seminormedAddCommGroup_topologicalSpace_eq_subtype,
        submodule_seminormedAddCommGroup_addCommMonoid_eq_natural,
        real_semifield_semiring_eq_natural,
        real_seminormedRing_addCommGroup_eq_natural,
        real_seminormedRing_pseudoMetricSpace_eq_natural,
        real_normedAddCommGroup_addGroup_eq_natural,
        real_normedAddCommGroup_pseudoMetricSpace_eq_natural,
        nativeSobolevSucc_normedAddCommGroup_eq_stage,
        nativeSobolevSucc_normedSpace_eq_stage,
        strong_real_nontriviallyNormedField_normedField_eq,
        harmonicSphereSubspace_normedSpace_module_eq_projected,
        hActualHarmonicModule,
        hHarmonicModule,
        sequenceLp_normedAddCommGroup_addCommMonoid_eq_natural,
        sequenceLp_normedSpace_module_eq_natural,
        strong_submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
        strong_submodule_seminormedAddCommGroup_topologicalSpace_eq,
        strong_submodule_seminormedAddCommGroup_addCommMonoid_eq,
        strong_submodule_normedSpace_module_eq,
        strong_lp_normedAddCommGroup_addCommMonoid_eq,
        strong_lp_normedSpace_module_eq,
        highStrongNativeH3Group,
        highStrongNativeH3Space,
        Nat.reduceAdd,
        SphereSobolev] using hNormalizedH3
    dbg_trace "STRONG_ADAPTER_ORIGINAL_NATIVE_TARGET_MATCH_RETURNED"


set_option diagnostics true in
def referenceHighSmoothMultiplierStrongDefectFamily (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (Q : SmoothCoefficientJets 3) (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] BallSobolev 3 := by
  exact {
    toFun := referenceHighSmoothMultiplierStrongDefectFunction g L y0 Φ B ε C ρ H a w hData hcalc hF Q p
    map_add' := referenceHighSmoothMultiplierStrongDefectFunction_map_add g L y0 Φ B ε C ρ H a w hData hcalc hF Q p
    map_smul' := by
      intro c f
      simpa only [RingHom.id_apply] using
        (referenceHighSmoothMultiplierStrongDefectFunction_map_smul g L y0 Φ B ε C ρ H a w hData hcalc hF Q p c f)
    cont := continuous_referenceHighSmoothMultiplierStrongDefectFunction g L y0 Φ B ε C ρ H a w hData hcalc hF Q p
  }


attribute [local irreducible] referenceHighSmoothMultiplierStrongDefectFamily

lemma lowerOrder_referenceHighSmoothMultiplierStrongDefectFamily
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (Q : SmoothCoefficientJets 3)
    (p : ℝ × (R3 × ℝ)) (lam Lam : ℝ)
    (hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (fun z => a (p,z)) lam Lam)
    (hsmall : ∀ z ∈ (ballOpens : Set R3),
      ‖conformalReferenceWeightedFramedDrift g L Φ H w (p,z)‖ ≤ lam/4)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (f : SphereSobolev (3/2 : ℝ)) :
    TauCeti.Wkp.lowerOrder 2
      (referenceHighSmoothMultiplierStrongDefectFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF Q p f) =
    referenceSmoothMultiplierStrongDefectFamily g L y0 Φ B ε C ρ H a w hData hcalc hF Q p
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) f) := by
  dbg_trace "STRONG_LOWER_BODY_ENTER"
  let U : BallSobolev 2 := referenceHarmonicLiftFamily
    g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2 (harmonicLiftCompletion hF f)
  dbg_trace "STRONG_LOWER_U_READY"
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let W := referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p
  let N := referenceSmoothMultiplierCommutatorForcingFamily g L y0 Φ B ε C ρ H a w hData hcalc Q p
  dbg_trace "STRONG_LOWER_INPUT_ALIASES_READY"
  let F : BallSobolev 1 := referenceHighSmoothMultiplierCommutatorForcingFamily
    g L y0 Φ B ε C ρ H a w hData hcalc Q p U
  dbg_trace "STRONG_LOWER_FORCING_VALUE_READY"
  let A : BallSobolev 0 →L[ℝ] BallSobolev 2 :=
    (strongDirichletSubmodule 0).toSubmodule.subtypeL.comp
      (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).inverse
  dbg_trace "STRONG_LOWER_A_READY"
  have hStrong := referenceStrongDriftFamily_isInvertible_of_smallDrift
    g L y0 Φ B ε C ρ H a w hData hcalc hreg 0 p.1 p.2 lam Lam hUE hsmall
  dbg_trace "STRONG_LOWER_STRONG_INVERTIBILITY_READY"
  have hU : TauCeti.Wkp.firstOrder 1 U = W (I f) :=
    firstOrder_referenceHarmonicLiftFamily_eq_weakHalfLift_of_isInvertible
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO τ0 p.1 p.2 hStrong hWeak f
  dbg_trace "STRONG_LOWER_HARMONIC_WEAK_GRAPH_READY"
  have hNative : TauCeti.Wkp.value 1 F = N (TauCeti.Wkp.firstOrder 1 U) := by
    dbg_trace "STRONG_LOWER_NATIVE_FORCING_PROOF_ENTER"
    have hF : F = nativeHighBulkMultiplierCommutatorForcingL hcalc
        (referenceCoordinateForcingPrincipalJets g L y0 Φ B ε C ρ H a w hData p)
        (referenceCoordinateForcingDriftJets g L y0 Φ B ε C ρ H a w hData p) Q U := rfl
    dbg_trace "STRONG_LOWER_NATIVE_FORCING_VALUE_GRAPH_READY"
    have hN : N (TauCeti.Wkp.firstOrder 1 U) =
        nativeBulkMultiplierCommutatorForcingL hcalc
          (referenceCoordinateForcingPrincipalJets g L y0 Φ B ε C ρ H a w hData p)
          (referenceCoordinateForcingDriftJets g L y0 Φ B ε C ρ H a w hData p) Q
          (TauCeti.Wkp.firstOrder 1 U) := by
      dsimp only [N]
      unfold referenceSmoothMultiplierCommutatorForcingFamily
      rfl
    dbg_trace "STRONG_LOWER_LOW_FORCING_VALUE_GRAPH_READY"
    exact (congrArg (fun V : BallSobolev 1 => TauCeti.Wkp.value 1 V) hF).trans
      ((value_nativeHighBulkMultiplierCommutatorForcingL hcalc
        (referenceCoordinateForcingPrincipalJets g L y0 Φ B ε C ρ H a w hData p)
        (referenceCoordinateForcingDriftJets g L y0 Φ B ε C ρ H a w hData p) Q U).trans hN.symm)
  dbg_trace "STRONG_LOWER_NATIVE_FORCING_GRAPH_RETURNED"
  have hForcing : TauCeti.Wkp.value 1 F = N (W (I f)) := hNative.trans (congrArg N hU)
  dbg_trace "STRONG_LOWER_WEAK_FORCING_GRAPH_READY"
  dbg_trace "STRONG_LOWER_HIGH_VALUE_DECL_ENTER"
  have hHigh : referenceHighSmoothMultiplierStrongDefectFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF Q p f =
      nativeStrongDirichletInverseInclusionL 1
        (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 p.1 p.2) F := by
    dbg_trace "STRONG_LOWER_HIGH_VALUE_PROOF_ENTER"
    unfold referenceHighSmoothMultiplierStrongDefectFamily
    exact referenceHighSmoothMultiplierStrongDefectFunction_apply
      g L y0 Φ B ε C ρ H a w hData hcalc hF Q p f
  dbg_trace "STRONG_LOWER_HIGH_VALUE_RETURNED"
  have hLow : referenceSmoothMultiplierStrongDefectFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF Q p (I f) = A (N (W (I f))) := by
    dbg_trace "STRONG_LOWER_LOW_VALUE_PROOF_ENTER"
    unfold referenceSmoothMultiplierStrongDefectFamily
    rfl
  dbg_trace "STRONG_LOWER_LOW_VALUE_RETURNED"
  dbg_trace "STRONG_LOWER_FINAL_COHERENCE_ENTER"
  exact (congrArg (fun V : BallSobolev 3 => TauCeti.Wkp.lowerOrder 2 V) hHigh).trans
    ((congrArg (fun V : BallSobolev 3 => TauCeti.Wkp.lowerOrder 2 V)
      (nativeStrongDirichletInverseInclusionL_apply 1
        (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 p.1 p.2) F)).trans
      ((lowerOrder_referenceStrongDriftFamily_inverse_one g L y0 Φ B ε C ρ H a w hData
        hcalc hreg p.1 p.2 lam Lam hUE hsmall F).trans ((congrArg A hForcing).trans hLow.symm)))
  dbg_trace "STRONG_LOWER_FINAL_COHERENCE_RETURNED"

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighSmoothMultiplierCommutatorForcingFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighSmoothMultiplierStrongDefectFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.lowerOrder_referenceHighSmoothMultiplierStrongDefectFamily

