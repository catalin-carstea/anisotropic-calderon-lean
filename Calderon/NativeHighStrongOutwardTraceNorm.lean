import Calderon.NativeHighStrongH3SourceNormTransport
import Calderon.NativeHighStrongOutwardTrace
import Calderon.InheritedNormedStructureData
import Calderon.SubmoduleRealNaturalStructureData

/-! The canonical operator norm from the full source data, with a local
registration of that Norm value only after its explicit construction. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeH3ThreeHalfRadialTrace

attribute [local instance_reducible] highStrongNativeH3Group
attribute [local instance_reducible] highStrongNativeH3Space
attribute [local instance] highStrongNativeH3Group
attribute [local instance] highStrongNativeH3Space
attribute [local irreducible] TauCeti.SobolevStage.instNormedAddCommGroup
attribute [local irreducible] TauCeti.SobolevStage.instNormedSpace

lemma nativeStageNormedSourceCarrier_eq_outward :
    normedSourceCLMCarrier (BallSobolev 3) (SphereSobolev (3/2 : ℝ)) nativeStageH3NormedSourceData =
    (@ContinuousLinearMap ℝ ℝ Real.semiring Real.semiring (RingHom.id ℝ)
      (BallSobolev 3)
      (TauCeti.SobolevStage.instNormedAddCommGroup
        (mu := (MeasureTheory.volume : MeasureTheory.Measure R3))
        (Omega := ballOpens) (p := 2) 2).toSeminormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      (TauCeti.SobolevStage.instNormedAddCommGroup
        (mu := (MeasureTheory.volume : MeasureTheory.Measure R3))
        (Omega := ballOpens) (p := 2) 2).toAddCommGroup.toAddCommMonoid
      (SphereSobolev (3/2 : ℝ))
      (inferInstance : TopologicalSpace (SphereSobolev (3/2 : ℝ)))
      (inferInstance : AddCommMonoid (SphereSobolev (3/2 : ℝ)))
      (@NormedSpace.toModule ℝ (BallSobolev 3) Real.normedField
        (@NormedAddCommGroup.toSeminormedAddCommGroup (BallSobolev 3)
          (TauCeti.SobolevStage.instNormedAddCommGroup
            (mu := (MeasureTheory.volume : MeasureTheory.Measure R3))
            (Omega := ballOpens) (p := 2) 2))
        (TauCeti.SobolevStage.instNormedSpace
          (mu := (MeasureTheory.volume : MeasureTheory.Measure R3))
          (Omega := ballOpens) (p := 2) 2))
      (inferInstance : Module ℝ (SphereSobolev (3/2 : ℝ)))) := by
  dsimp only [normedSourceCLMCarrier, nativeStageH3NormedSourceData]
  all_goals simp only [real_nontriviallyNormedField_normedField_eq,
      submodule_normedAddCommGroup_seminormedAddCommGroup_eq_independent,
      submodule_seminormedAddCommGroup_topologicalSpace_eq_subtype,
      submodule_seminormedAddCommGroup_addCommMonoid_eq_natural,
      submodule_normedSpace_module_eq]
  all_goals rfl

lemma nativeChosenNormedSourceCarrier_eq_outward :
    normedSourceCLMCarrier (BallSobolev 3) (SphereSobolev (3/2 : ℝ)) nativeHighStrongH3NormedSourceData =
      (BallSobolev 3 →L[ℝ] SphereSobolev (3/2 : ℝ)) := by
  dsimp only [normedSourceCLMCarrier, nativeHighStrongH3NormedSourceData]
  all_goals simp only [real_nontriviallyNormedField_normedField_eq,
      submodule_normedAddCommGroup_seminormedAddCommGroup_eq_independent,
      submodule_seminormedAddCommGroup_topologicalSpace_eq_subtype,
      submodule_seminormedAddCommGroup_addCommMonoid_eq_natural,
      submodule_normedSpace_module_eq]
  all_goals rfl

lemma nativeChosenNormedSourceNorm_eq_outward :
    Eq.mp (congrArg (fun A : Type => Norm A)
        nativeChosenNormedSourceCarrier_eq_outward)
      (normedSourceCLMNorm (BallSobolev 3) (SphereSobolev (3/2 : ℝ)) nativeHighStrongH3NormedSourceData) =
      (inferInstance : Norm (BallSobolev 3 →L[ℝ] SphereSobolev (3/2 : ℝ))) := by
  rfl

def nativeOutwardStageCanonicalNorm : Norm
    (@ContinuousLinearMap ℝ ℝ Real.semiring Real.semiring (RingHom.id ℝ)
      (BallSobolev 3)
      (TauCeti.SobolevStage.instNormedAddCommGroup
        (mu := (MeasureTheory.volume : MeasureTheory.Measure R3))
        (Omega := ballOpens) (p := 2) 2).toSeminormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      (TauCeti.SobolevStage.instNormedAddCommGroup
        (mu := (MeasureTheory.volume : MeasureTheory.Measure R3))
        (Omega := ballOpens) (p := 2) 2).toAddCommGroup.toAddCommMonoid
      (SphereSobolev (3/2 : ℝ))
      (inferInstance : TopologicalSpace (SphereSobolev (3/2 : ℝ)))
      (inferInstance : AddCommMonoid (SphereSobolev (3/2 : ℝ)))
      (@NormedSpace.toModule ℝ (BallSobolev 3) Real.normedField
        (@NormedAddCommGroup.toSeminormedAddCommGroup (BallSobolev 3)
          (TauCeti.SobolevStage.instNormedAddCommGroup
            (mu := (MeasureTheory.volume : MeasureTheory.Measure R3))
            (Omega := ballOpens) (p := 2) 2))
        (TauCeti.SobolevStage.instNormedSpace
          (mu := (MeasureTheory.volume : MeasureTheory.Measure R3))
          (Omega := ballOpens) (p := 2) 2))
      (inferInstance : Module ℝ (SphereSobolev (3/2 : ℝ)))) :=
  Eq.mp (congrArg (fun A : Type => Norm A)
      nativeStageNormedSourceCarrier_eq_outward)
    (normedSourceCLMNorm (BallSobolev 3) (SphereSobolev (3/2 : ℝ)) nativeStageH3NormedSourceData)

lemma nativeHighStrongOutwardTraceL_eq_normedSource_transport
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    nativeHighStrongOutwardTraceL hcalc hF hO hD τ0 =
    Eq.mp nativeChosenNormedSourceCarrier_eq_outward
      (Eq.mp (congrArg (normedSourceCLMCarrier (BallSobolev 3) (SphereSobolev (3/2 : ℝ)))
          nativeHighStrongH3NormedSourceData_eq_stage.symm)
        (Eq.mpr nativeStageNormedSourceCarrier_eq_outward
          (Eq.mp (nativeOutwardActualCarrier_eq_stage hcalc hF hO hD τ0)
            (nativeThreeHalfOutwardTraceL hcalc hF hO hD τ0 :
      nativeOutwardActualCarrier hcalc hF hO hD τ0)))) := by
  have hChain {A B C D E : Type} (hAB : A = B) (hCB : C = B)
      (hCD : C = D) (hDE : D = E) (hAE : A = E) (x : A) :
      Eq.mp hAE x = Eq.mp hDE (Eq.mp hCD (Eq.mpr hCB (Eq.mp hAB x))) := by
    cases hAB
    cases hCB
    cases hCD
    cases hDE
    rfl
  exact hChain (nativeOutwardActualCarrier_eq_stage hcalc hF hO hD τ0)
    nativeStageNormedSourceCarrier_eq_outward
    (congrArg (normedSourceCLMCarrier (BallSobolev 3) (SphereSobolev (3/2 : ℝ)))
      nativeHighStrongH3NormedSourceData_eq_stage.symm)
    nativeChosenNormedSourceCarrier_eq_outward
    (nativeOutwardActualCarrier_eq_native hcalc hF hO hD τ0)
    (nativeThreeHalfOutwardTraceL hcalc hF hO hD τ0 :
      nativeOutwardActualCarrier hcalc hF hO hD τ0)

lemma opNorm_nativeHighStrongOutwardTraceL_eq_stage
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    ContinuousLinearMap.opNorm (nativeHighStrongOutwardTraceL hcalc hF hO hD τ0) =
      @norm _ nativeOutwardStageCanonicalNorm
        (Eq.mp (nativeOutwardActualCarrier_eq_stage hcalc hF hO hD τ0)
        (nativeThreeHalfOutwardTraceL hcalc hF hO hD τ0 :
      nativeOutwardActualCarrier hcalc hF hO hD τ0)) := by
  have hForward {A B : Type} (e : A = B) (n : Norm A) (x : A) :
      @norm B (Eq.mp (congrArg (fun T : Type => Norm T) e) n)
          (Eq.mp e x) = @norm A n x := by
    cases e
    rfl
  have hBackward {A B : Type} (e : A = B) (n : Norm A) (y : B) :
      @norm B (Eq.mp (congrArg (fun T : Type => Norm T) e) n) y =
        @norm A n (Eq.mpr e y) := by
    cases e
    rfl
  let actualValue : nativeOutwardActualCarrier hcalc hF hO hD τ0 :=
    nativeThreeHalfOutwardTraceL hcalc hF hO hD τ0
  let stageValue := Eq.mp (nativeOutwardActualCarrier_eq_stage hcalc hF hO hD τ0) actualValue
  let genericStageValue := Eq.mpr nativeStageNormedSourceCarrier_eq_outward stageValue
  let chosenValue := Eq.mp (congrArg (normedSourceCLMCarrier (BallSobolev 3) (SphereSobolev (3/2 : ℝ)))
    nativeHighStrongH3NormedSourceData_eq_stage.symm) genericStageValue
  have hPublic := hForward nativeChosenNormedSourceCarrier_eq_outward
    (normedSourceCLMNorm (BallSobolev 3) (SphereSobolev (3/2 : ℝ)) nativeHighStrongH3NormedSourceData) chosenValue
  rw [nativeChosenNormedSourceNorm_eq_outward] at hPublic
  have hStage := hBackward nativeStageNormedSourceCarrier_eq_outward
    (normedSourceCLMNorm (BallSobolev 3) (SphereSobolev (3/2 : ℝ)) nativeStageH3NormedSourceData) stageValue
  have hData := normedSourceCLMNorm_nativeHighStrong_transport genericStageValue
  have hValue := nativeHighStrongOutwardTraceL_eq_normedSource_transport hcalc hF hO hD τ0
  have hNormValue := congrArg
    (fun T : (BallSobolev 3 →L[ℝ] SphereSobolev (3/2 : ℝ)) => ContinuousLinearMap.opNorm T) hValue
  exact hNormValue.trans (hPublic.trans (hData.trans hStage.symm))

attribute [local instance] nativeOutwardStageCanonicalNorm

lemma norm_nativeThreeHalfOutwardTraceL_eq_stage
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    ‖nativeThreeHalfOutwardTraceL hcalc hF hO hD τ0‖ =
      @norm _ nativeOutwardStageCanonicalNorm
        (Eq.mp (nativeOutwardActualCarrier_eq_stage hcalc hF hO hD τ0)
        (nativeThreeHalfOutwardTraceL hcalc hF hO hD τ0 :
      nativeOutwardActualCarrier hcalc hF hO hD τ0)) := by
  rfl

lemma opNorm_nativeHighStrongOutwardTraceL_eq_original
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    ContinuousLinearMap.opNorm (nativeHighStrongOutwardTraceL hcalc hF hO hD τ0) =
      ‖nativeThreeHalfOutwardTraceL hcalc hF hO hD τ0‖ := by
  exact (opNorm_nativeHighStrongOutwardTraceL_eq_stage hcalc hF hO hD τ0).trans
    (norm_nativeThreeHalfOutwardTraceL_eq_stage hcalc hF hO hD τ0).symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeStageNormedSourceCarrier_eq_outward
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeChosenNormedSourceCarrier_eq_outward
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeChosenNormedSourceNorm_eq_outward
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeOutwardStageCanonicalNorm
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeHighStrongOutwardTraceL_eq_normedSource_transport
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.opNorm_nativeHighStrongOutwardTraceL_eq_stage
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.norm_nativeThreeHalfOutwardTraceL_eq_stage
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.opNorm_nativeHighStrongOutwardTraceL_eq_original
