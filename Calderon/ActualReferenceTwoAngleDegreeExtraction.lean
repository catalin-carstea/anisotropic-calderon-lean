import Calderon.ActualReferenceTwoAngleDegreeCasimirDataTopology
import Calderon.PhysicalDegreeCasimirSmoothRestriction
import Calderon.PhysicalDegreeCasimirExtractorSmoothNorm
import Calderon.PhysicalDegreeCasimirHalfExtractor
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! Actual closed-data extraction. -/
set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic PhysicalDegreeCasimirCompatibility
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
  (k l : Fin 3)

def referenceTwoAngleDegreeCasimirCompatibleDataFamily :
    (ℝ × (ℝ × (R3 × ℝ))) → physicalDegreeCasimirCompatibleData hO hD :=
  physicalDegreeCasimirRestriction hO hD
    (referenceTwoAnglePhysicalDegreeCasimirDataFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l)
    (referenceTwoAngleDegreeDataInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 k l)
    (fun z hz => (mem_physicalDegreeCasimirCompatibleData_iff hO hD _).1
      (referenceTwoAnglePhysicalDegreeCasimirDataFamily_mem
        g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l z.1 z.2
          (fun i j => Set.mem_iInter.mp hz (i,j))))

attribute [local irreducible] referenceTwoAnglePhysicalDegreeCasimirDataFamily
  referenceTwoAngleSharpRadialTraceFamily referenceTwoAngleLowerRadialEndpointFamily
  sphereSobolevShiftedDegreeL sphereSobolevInclusionL

lemma referenceTwoAngleDegreeCasimirCompatibleDataFamily_coe
    (z : ℝ × (ℝ × (R3 × ℝ)))
    (hz : z ∈ referenceTwoAngleDegreeDataInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 k l) :
    (referenceTwoAngleDegreeCasimirCompatibleDataFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l z : PhysicalDegreeCasimirData) =
    referenceTwoAnglePhysicalDegreeCasimirDataFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l z :=
  physicalDegreeCasimirRestriction_coe_of_mem hO hD
    (referenceTwoAnglePhysicalDegreeCasimirDataFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l)
    (referenceTwoAngleDegreeDataInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 k l)
    (fun t ht => (mem_physicalDegreeCasimirCompatibleData_iff hO hD _).1
      (referenceTwoAnglePhysicalDegreeCasimirDataFamily_mem
        g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l t.1 t.2
          (fun i j => Set.mem_iInter.mp ht (i,j)))) z hz

lemma contDiffOn_referenceTwoAngleDegreeCasimirCompatibleDataFamily :
    ContDiffOn ℝ ∞ (referenceTwoAngleDegreeCasimirCompatibleDataFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l)
      (referenceTwoAngleDegreeDataInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 k l) :=
  contDiffOn_physicalDegreeCasimirRestriction hO hD
    (referenceTwoAnglePhysicalDegreeCasimirDataFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l)
    (referenceTwoAngleDegreeDataInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 k l)
    (isOpen_referenceTwoAngleDegreeDataInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 k l)
    (fun z hz => (mem_physicalDegreeCasimirCompatibleData_iff hO hD _).1
      (referenceTwoAnglePhysicalDegreeCasimirDataFamily_mem
        g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l z.1 z.2
          (fun i j => Set.mem_iInter.mp hz (i,j))))
    (contDiffOn_referenceTwoAnglePhysicalDegreeCasimirDataFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 k l hreg)

def referenceTwoAngleDegreeCommutatorHalfFamily
    (z : ℝ × (ℝ × (R3 × ℝ))) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  compatibleDegreeHalfExtractorL hO hD
    (referenceTwoAngleDegreeCasimirCompatibleDataFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l z)

lemma contDiffOn_referenceTwoAngleDegreeCommutatorHalfFamily :
    ContDiffOn ℝ ∞ (referenceTwoAngleDegreeCommutatorHalfFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l)
      (referenceTwoAngleDegreeDataInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 k l) := by
  have hExtract := contDiff_compatibleDegreeHalfExtractorL hO hD
  have hDataSmooth := contDiffOn_referenceTwoAngleDegreeCasimirCompatibleDataFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l
  exact ContDiff.comp_contDiffOn hExtract hDataSmooth

lemma contDiffAt_referenceTwoAngleDegreeCommutatorHalfFamily
    (z : ℝ × (ℝ × (R3 × ℝ)))
    (hz : z ∈ referenceTwoAngleDegreeDataInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 k l) :
    ContDiffAt ℝ ∞ (referenceTwoAngleDegreeCommutatorHalfFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l) z :=
  (contDiffOn_referenceTwoAngleDegreeCommutatorHalfFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l).contDiffAt
      ((isOpen_referenceTwoAngleDegreeDataInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 k l).mem_nhds hz)

lemma referenceTwoAngleDegreeCommutatorHalfFamily_raw_high_graph
    (z : ℝ × (ℝ × (R3 × ℝ)))
    (hz : z ∈ referenceTwoAngleDegreeDataInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 k l)
    (u : SphereSobolev (3/2:ℝ)) :
    referenceTwoAngleDegreeCommutatorHalfFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l z
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u) =
    sphereSobolevShiftedDegreeL (1/2:ℝ)
      (referenceTwoAngleSharpRadialTraceFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 0 0 k l (0,z) u) -
    referenceTwoAngleLowerRadialEndpointFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 0 0 k l (0,z)
      (sphereSobolevShiftedDegreeL (3/2:ℝ) u) := by
  let x := referenceTwoAngleDegreeCasimirCompatibleDataFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l z
  have hCoe : (x : PhysicalDegreeCasimirData) = referenceTwoAnglePhysicalDegreeCasimirDataFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l z :=
    referenceTwoAngleDegreeCasimirCompatibleDataFamily_coe
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l z hz
  have hGraph := compatibleDegreeHalfExtractorL_high_graph hO hD x u
  have hRaw := congrArg (fun X : PhysicalDegreeCasimirData => degreeRawHighDataL X u) hCoe
  have hValue : degreeRawHighDataL (referenceTwoAnglePhysicalDegreeCasimirDataFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l z) u =
      sphereSobolevShiftedDegreeL (1/2:ℝ)
        (referenceTwoAngleSharpRadialTraceFamily
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 0 0 k l (0,z) u) -
      referenceTwoAngleLowerRadialEndpointFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 0 0 k l (0,z)
        (sphereSobolevShiftedDegreeL (3/2:ℝ) u) := by
    simp only [degreeRawHighDataL_apply,referenceTwoAnglePhysicalDegreeCasimirDataFamily,
      referenceTwoAngleRadialEndpointPairFamily,ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.comp_apply]
  exact hGraph.trans (hRaw.trans hValue)

lemma norm_referenceTwoAngleDegreeCommutatorHalfFamily_le_data_norm
    (z : ℝ × (ℝ × (R3 × ℝ)))
    (hz : z ∈ referenceTwoAngleDegreeDataInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 k l) :
    ‖referenceTwoAngleDegreeCommutatorHalfFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l z‖ ≤
    12*Real.sqrt 2*‖referenceTwoAnglePhysicalDegreeCasimirDataFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l z‖ := by
  let x := referenceTwoAngleDegreeCasimirCompatibleDataFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l z
  have hCoe : (x : PhysicalDegreeCasimirData) = referenceTwoAnglePhysicalDegreeCasimirDataFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l z :=
    referenceTwoAngleDegreeCasimirCompatibleDataFamily_coe
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l z hz
  have hNorm := norm_compatibleDegreeCasimirData_eq_of_coe_eq hO hD x _ hCoe
  exact (norm_compatibleDegreeHalfExtractorL_apply_le hO hD x).trans_eq
    (congrArg (fun r : ℝ => 12*Real.sqrt 2*r) hNorm)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleDegreeCasimirCompatibleDataFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleDegreeCasimirCompatibleDataFamily_coe
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffOn_referenceTwoAngleDegreeCasimirCompatibleDataFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleDegreeCommutatorHalfFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffOn_referenceTwoAngleDegreeCommutatorHalfFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceTwoAngleDegreeCommutatorHalfFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleDegreeCommutatorHalfFamily_raw_high_graph
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.norm_referenceTwoAngleDegreeCommutatorHalfFamily_le_data_norm
