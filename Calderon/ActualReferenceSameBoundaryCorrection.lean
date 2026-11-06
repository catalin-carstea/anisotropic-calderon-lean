import Calderon.UnitBallValueTraceKernel
import Calderon.NativeThreeHalfCoefficientMultiplier
import Calderon.ActualReferenceInvertibleStrongWeakCoherence

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
SAME-BOUNDARY-CORRECTION-EXPANSION-v001.md. Explicit adopted trace-kernel parameter only. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeH2ThreeHalfValueTrace
  NativeThreeHalfCoefficientMultiplier NativeHarmonicLiftCompletion
  NativeHarmonicH1LiftCompletion NativeHarmonicLiftOrderCoherence
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem firstOrder_sub_harmonicLiftCompletion_nativeThreeHalfTrace_mem_zero
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (hKernel : UnitBallValueTraceKernel τ0)
    (E : BallSobolev 2) :
    TauCeti.Wkp.firstOrder 1
      (E-harmonicLiftCompletion hF (nativeThreeHalfValueTraceL hcalc hF hO hD τ0 E)) ∈
      TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 := by
  let f := nativeThreeHalfValueTraceL hcalc hF hO hD τ0 E
  let Q : BallSobolev 2 →L[ℝ] BallH1 := TauCeti.Wkp.firstOrderL 1
  let Z := sphereSobolevZeroEquiv hO hD
  let I := sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num)
  have hTrace : I f = Z (τ0.valueTraceL (Q E)) :=
    sphereSobolevInclusionL_nativeThreeHalfValueTraceL_zero hcalc hF hO hD τ0 E
  have hFree : τ0.valueTraceL (Q (harmonicLiftCompletion hF f)) = Z.symm (I f) :=
    valueTraceL_harmonicH2LiftCompletion_coarse hF hO hD τ0 f
  have hSame : τ0.valueTraceL (Q (harmonicLiftCompletion hF f)) = τ0.valueTraceL (Q E) :=
    hFree.trans ((congrArg Z.symm hTrace).trans (Z.symm_apply_apply _))
  have hActualZero : τ0.valueTraceL (Q (E-harmonicLiftCompletion hF f)) = 0 := by
    rw [map_sub, map_sub, hSame, sub_self]
  exact (hKernel _).mp hActualZero

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

attribute [local irreducible] referenceHarmonicLiftFamily referenceWeakHalfLiftFamily
  referenceStrongDriftFamily referenceWeakDirichletEnergyFamily

theorem referenceHarmonicLiftFamily_eq_harmonicLiftCompletion_nativeThreeHalfTrace
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (hKernel : UnitBallValueTraceKernel τ0)
    (q : ℝ) (p : R3 × ℝ)
    (hStrong : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q p).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc (q,p)).IsInvertible)
    (E : BallSobolev 2) :
    referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q p E =
    referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q p
      (harmonicLiftCompletion hF (nativeThreeHalfValueTraceL hcalc hF hO hD τ0 E)) := by
  let f := nativeThreeHalfValueTraceL hcalc hF hO hD τ0 E
  let E0 := harmonicLiftCompletion hF f
  let V := referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q p E
  let Q : BallSobolev 2 →L[ℝ] BallH1 := TauCeti.Wkp.firstOrderL 1
  have hBase : Q (E-E0) ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 :=
    firstOrder_sub_harmonicLiftCompletion_nativeThreeHalfTrace_mem_zero hcalc hF hO hD τ0 hKernel E
  have hCorrection : Q (V-E) ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 :=
    referenceHarmonicLiftFamily_boundary_difference g L y0 Φ B ε C ρ H a w hData hcalc 0 q p hStrong E
  have hZero : Q (V-E0) ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 := by
    have hAlgebra : Q (V-E0) = Q (V-E) + Q (E-E0) := by
      simp only [map_sub]
      abel
    rw [hAlgebra]
    exact (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).add_mem hCorrection hBase
  have hBoundary : harmonicFirstOrderLiftCompletion hF
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) f) - Q V ∈
      TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 := by
    have hn : -(Q (V-E0)) ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 :=
      (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).neg_mem hZero
    have hElement : -(Q (V-E0)) =
        harmonicFirstOrderLiftCompletion hF
          (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) f) - Q V := by
      rw [map_sub, neg_sub]
      exact congrArg (fun z : BallH1 => z-Q V) (firstOrder_harmonicLiftCompletion hF hO f)
    exact (congrArg (fun z : BallH1 =>
      z ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2) hElement).mp hn
  have hAny : Q V = referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF (q,p)
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) f) :=
    eq_referenceWeakHalfLiftFamily_of_weak_energy_isInvertible
      g L y0 Φ B ε C ρ H a w hData hcalc hF (q,p) hWeak _ (Q V) hBoundary
      (fun v => referenceHarmonicLiftFamily_weak_energy_of_isInvertible
        g L y0 Φ B ε C ρ H a w hData hcalc τ0 q p hStrong E v)
  have hReference := firstOrder_referenceHarmonicLiftFamily_eq_weakHalfLift_of_isInvertible
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO τ0 q p hStrong hWeak f
  have hFirst : TauCeti.Wkp.firstOrder 1 V = TauCeti.Wkp.firstOrder 1
      (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q p E0) :=
    hAny.trans hReference.symm
  apply TauCeti.Wkp.ext 2
  have hValue := congrArg (fun u : BallH1 => TauCeti.W1p.value u) hFirst
  simpa only [TauCeti.Wkp.value_firstOrder] using hValue

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.firstOrder_sub_harmonicLiftCompletion_nativeThreeHalfTrace_mem_zero
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHarmonicLiftFamily_eq_harmonicLiftCompletion_nativeThreeHalfTrace
