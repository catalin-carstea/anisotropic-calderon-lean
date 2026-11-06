import Calderon.ActualFinitePhysicalModelErrorDictionary
import Calderon.ActualPhysicalLowResidualIntegralCap
import Calderon.ActualNativeMovingAdjointMixedJPointGraph

set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.MainPhysicalGraphBridge
open Set Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore
  ActualFiniteHarmonicModel ReferenceDensityBounds ReferenceWeightedApproximation ConformalDepth

theorem nativeMixedJOut_negative_graph_of_mem_closedBall
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (hreg : FixedDirichletRegularity)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (dr Ar : ℝ) (p : ℕ) (F0 : smoothCompactFiniteSphereCore hO hD)
    (y : R3) (hy : ‖y-y0‖ ≤ ρ) :
    let R : R3 → ℝ := referenceRadius dr Ar p L
    let u : R3 → SphereSobolev (3/2 : ℝ) := finiteCoreSobolevLift hO hD (3/2 : ℝ) F0
    let K : SphereL2 →L[ℝ] SphereSobolev (-(1/2 : ℝ)) := (sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)).comp
      (sphereSobolevZeroEquiv hO hD).toContinuousLinearEquiv.toContinuousLinearMap
    let Iin : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
    let Iout : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
    let Ahi : Fin 3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := fun i : Fin 3 => sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) i
    let Alo : Fin 3 → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) := fun i : Fin 3 => sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i
    let Fh := fun (i : Fin 3) (x : R3) => referenceNativeMovingAdjointParametricCorrection
      hF hO hD g L (3/2 : ℝ) ((q,x),fderiv ℝ R x) i
    let Fl := fun i : Fin 3 => referenceNativeMovingAdjointParametricCorrection
      hF hO hD g L (1/2 : ℝ) ((q,y),fderiv ℝ R y) i
    let F := fun (i : Fin 3) (x : R3) => Iin (Fh i x (u x))
    let MF := fun i : Fin 3 => Iout.comp (Fl i)
    let Q := fun i j : Fin 3 => referenceDensityPrincipalFrameCoefficient g g2 L q y i j
    let JF : SphereSobolev (-(1/2 : ℝ)) := ∑ i : Fin 3, ∑ j : Fin 3, Q i j •
      (Alo i (F j y)+MF i (Ahi j (u y)))
    K (nativeMixedJOut hF hO hD g g2 L q dr Ar p F0 y) =
      K ((nativeModelRaisingDrift hO hD hF g g2 hg hg2 L q F0).val y) + JF := by
  classical
  intro R u K0 dIin dIout dAhi dAlo dFh dFl dF dMF dQ dJF
  let Drift : R3 → SphereL2 :=
    (nativeModelRaisingDrift hO hD hF g g2 hg hg2 L q F0).val
  have hPoint := referenceNativeMovingAdjointParametricJ_lift_negative_graph
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 g2 hreg
    q hq y (fderiv ℝ R y) (u y) (Or.inl hy)
  have hSplit := referenceNativeMovingAdjointHighMixedCorrection_finiteCore_split
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
    hg g2 hg2 hreg q hq F0 y hy (fderiv ℝ R y)
  -- Isolate the split's nine fixed-point lets before matching the full dictionary.
  extract_lets (merge := false) (useContext := false) (descend := false)
    j_u j_I j_J j_K j_Ah j_Al j_Fh j_Fl j_JF at hSplit
  have hKPointEvaluation (v : SphereL2) : K0 v =
      sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
        (sphereSobolevZeroEquiv hO hD v) := by
    rfl
  have hJPointValue : nativeMixedJOut hF hO hD g g2 L q dr Ar p F0 y =
      (sphereSobolevZeroEquiv hO hD).symm
        (referenceNativeMovingAdjointParametricJ hF hO hD g g2 L
          ((q,y),fderiv ℝ R y)
          (sphereSobolevInclusionL (3/2 : ℝ) 1 (by norm_num) (u y))) := by
    dsimp only [nativeMixedJOut, R, u] <;> rfl
  have hJPointValueMapped := congrArg
    (fun v : SphereL2 => sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
      (sphereSobolevZeroEquiv hO hD v)) hJPointValue
  have hJLeft :=
    (hKPointEvaluation (nativeMixedJOut hF hO hD g g2 L q dr Ar p F0 y)).trans hJPointValueMapped
  have hJPointInferred := hJLeft.trans hPoint
  have hJPointForSplit := hJPointInferred
  dsimp only [u] at hJPointForSplit
  have hSplitFixed := hSplit
  dsimp only [j_J, j_u] at hSplitFixed
  have hJInferred := hJPointForSplit.trans hSplitFixed
  have hDriftFixed :
      j_K ((nativeModelRaisingDrift hO hD hF g g2 hg hg2 L q F0).val y) =
        K0 (Drift y) := by
    rfl
  have hJFAligned : j_JF = dJF := by
    simp only [j_JF,j_Al,j_I,j_Fh,j_J,j_Fl,j_Ah,j_u,
      dJF,dQ,dAlo,dF,dIin,dFh,dMF,dIout,dFl,dAhi,u,R,
      ContinuousLinearMap.comp_apply]
  have hJRight :
      j_K ((nativeModelRaisingDrift hO hD hF g g2 hg hg2 L q F0).val y) + j_JF =
        K0 (Drift y) + dJF :=
    congrArg₂ (fun z t : SphereSobolev (-(1/2 : ℝ)) => z + t)
      hDriftFixed hJFAligned
  have hJ : K0 (nativeMixedJOut hF hO hD g g2 L q dr Ar p F0 y) =
      K0 (Drift y) + dJF := hJInferred.trans hJRight
  exact hJ

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.MainPhysicalGraphBridge
