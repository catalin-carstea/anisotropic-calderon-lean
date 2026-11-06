import Calderon.ActualReferenceTwoAngleWeakOperatorContinuity
import Calderon.NativeTwoAngleInverseOpenCanonical
import Calderon.ActualReferenceTwoAngleFullWeakEnergyTopology
import Calderon.ActualReferenceRotationWeakEnergy
import Calderon.InheritedNormedStructureData
import Calderon.ClmInheritedStructureData
import Calderon.ClmNaturalStructureData
import Calderon.SubmoduleRealNaturalStructureData
import Calderon.NativeWeakOperatorNormedStructures
import Calderon.NativeTwoAngleDualTestPostcompositionTopology

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace


attribute [local instance]
  weakHeaderDualH1Group
  weakHeaderDualH1Space
  weakHeaderDualZeroGroup
  weakHeaderDualZeroSpace
  weakHeaderH1DualZeroGroup
  weakHeaderH1DualZeroSpace
  weakHeaderSelfDualGroup
  weakHeaderSelfDualSpace
  weakHeaderDualZeroH1ZeroGroup
  weakHeaderDualZeroH1ZeroSpace

attribute [local irreducible] referenceTwoAngleFullWeakEnergyFamily
  referenceTwoAngleWeakEnergyFamily referenceTwoAngleWeakDirichletEnergyFamily

lemma isOpen_referenceTwoAngleWeak_inverse_set (hcalc : FixedSobolevCalculus)
    (i j k l : Fin 3) :
    IsOpen {t : ℝ × (ℝ × (ℝ × (R3 × ℝ))) |
      (referenceTwoAngleWeakDirichletEnergyFamily
        g L y0 Φ B ε C ρ H a w hData hcalc i j k l t).IsInvertible} := by
  exact isOpen_nativeTwoAngle_inverse_preimage_canonical
    (referenceTwoAngleWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l)
    (contDiff_referenceTwoAngleWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc i j k l)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.isOpen_referenceTwoAngleWeak_inverse_set
